// Lean compiler output
// Module: Std.Time.Notation
// Imports: public import Std.Time.Format public meta import Std.Time.Format
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Syntax_mkNumLit(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getString(lean_object*);
lean_object* l_Std_Time_PlainDateTime_fromLeanDateTimeString(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkStrLit(lean_object*, lean_object*);
lean_object* lean_thunk_get_own(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Time_DateTime_fromLeanDateTimeWithZoneString(lean_object*);
lean_object* l_Std_Time_DateTime_fromLeanDateTimeWithIdentifierString(lean_object*);
lean_object* l_Std_Time_TimeZone_fromTimeZone(lean_object*);
lean_object* l_Std_Time_PlainDate_fromSQLDateString(lean_object*);
lean_object* l_Std_Time_TimeZone_Offset_fromOffset(lean_object*);
lean_object* l_Std_Time_PlainTime_fromLeanTime24Hour(lean_object*);
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertText___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Text.short"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertText___closed__0 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__0_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertText___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertText___closed__1;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Time"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertText___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Text"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertText___closed__4 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__4_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertText___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "short"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertText___closed__5 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__5_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertText___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertText___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__6_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertText___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__6_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__4_value),LEAN_SCALAR_PTR_LITERAL(173, 214, 90, 117, 56, 8, 198, 188)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertText___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__6_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__5_value),LEAN_SCALAR_PTR_LITERAL(26, 39, 135, 112, 213, 217, 93, 143)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertText___closed__6 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__6_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertText___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertText___closed__7 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__7_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertText___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__6_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertText___closed__8 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__8_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertText___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertText___closed__9 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__9_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertText___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__7_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__9_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertText___closed__10 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__10_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertText___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Std.Time.Text.full"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertText___closed__11 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__11_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertText___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertText___closed__12;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertText___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "full"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertText___closed__13 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__13_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertText___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertText___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__14_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertText___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__14_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__4_value),LEAN_SCALAR_PTR_LITERAL(173, 214, 90, 117, 56, 8, 198, 188)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertText___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__14_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__13_value),LEAN_SCALAR_PTR_LITERAL(249, 161, 82, 63, 128, 99, 134, 35)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertText___closed__14 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__14_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertText___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__14_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertText___closed__15 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__15_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertText___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__14_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertText___closed__16 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__16_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertText___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__16_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertText___closed__17 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__17_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertText___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__15_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__17_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertText___closed__18 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__18_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertText___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Std.Time.Text.narrow"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertText___closed__19 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__19_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertText___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertText___closed__20;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertText___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "narrow"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertText___closed__21 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__21_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertText___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertText___closed__22_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__22_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertText___closed__22_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__22_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__4_value),LEAN_SCALAR_PTR_LITERAL(173, 214, 90, 117, 56, 8, 198, 188)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertText___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__22_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__21_value),LEAN_SCALAR_PTR_LITERAL(222, 165, 179, 214, 155, 106, 191, 242)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertText___closed__22 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__22_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertText___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__22_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertText___closed__23 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__23_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertText___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__22_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertText___closed__24 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__24_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertText___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__24_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertText___closed__25 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__25_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertText___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__23_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__25_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertText___closed__26 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__26_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertText(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertText___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__0 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__0_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__1 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__1_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__2 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__2_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__3 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__3_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__3_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Std.Time.Number.mk"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__5 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__5_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__6;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Number"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__7 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__7_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__8 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__8_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__9_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__9_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__7_value),LEAN_SCALAR_PTR_LITERAL(149, 31, 30, 146, 171, 66, 77, 169)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__9_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__8_value),LEAN_SCALAR_PTR_LITERAL(17, 215, 130, 19, 65, 152, 2, 206)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__9 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__9_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__10 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__10_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__9_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__11 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__11_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__11_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__12 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__12_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__10_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__12_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__13 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__13_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__14 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__14_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__14_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertNumber(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertNumber___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Std.Time.Fraction.nano"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__0 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__0_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__1;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Fraction"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__2 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__2_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "nano"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__3 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__3_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__4_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__4_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(174, 147, 200, 1, 236, 88, 4, 2)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__4_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__3_value),LEAN_SCALAR_PTR_LITERAL(135, 130, 55, 186, 177, 120, 199, 35)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__4 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__4_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__5 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__5_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__4_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__6 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__6_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__7 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__7_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__5_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__7_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__8 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__8_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Std.Time.Fraction.truncated"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__9 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__9_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__10;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "truncated"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__11 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__11_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__12_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__12_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(174, 147, 200, 1, 236, 88, 4, 2)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__12_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__11_value),LEAN_SCALAR_PTR_LITERAL(245, 244, 158, 231, 210, 230, 8, 254)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__12 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__12_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__12_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__13 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__13_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__12_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__14 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__14_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__14_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__15 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__15_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__13_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__15_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__16 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__16_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertFraction(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertFraction___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Std.Time.Year.any"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__0 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__0_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__1;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Year"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__2 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__2_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "any"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__3 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__3_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__4_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__4_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__2_value),LEAN_SCALAR_PTR_LITERAL(81, 61, 104, 127, 147, 223, 116, 59)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__4_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__3_value),LEAN_SCALAR_PTR_LITERAL(177, 87, 37, 32, 28, 199, 229, 134)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__4 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__4_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__5 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__5_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__4_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__6 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__6_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__7 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__7_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__5_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__7_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__8 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__8_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Std.Time.Year.twoDigit"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__9 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__9_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__10;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "twoDigit"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__11 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__11_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__12_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__12_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__2_value),LEAN_SCALAR_PTR_LITERAL(81, 61, 104, 127, 147, 223, 116, 59)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__12_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__11_value),LEAN_SCALAR_PTR_LITERAL(10, 27, 61, 34, 208, 129, 36, 157)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__12 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__12_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__12_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__13 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__13_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__12_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__14 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__14_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__14_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__15 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__15_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__13_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__15_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__16 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__16_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Std.Time.Year.fourDigit"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__17 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__17_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__18;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "fourDigit"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__19 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__19_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__20_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__20_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__2_value),LEAN_SCALAR_PTR_LITERAL(81, 61, 104, 127, 147, 223, 116, 59)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__20_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__19_value),LEAN_SCALAR_PTR_LITERAL(251, 28, 132, 113, 104, 79, 27, 228)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__20 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__20_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__20_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__21 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__21_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__20_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__22 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__22_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__22_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__23 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__23_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__21_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__23_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__24 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__24_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Std.Time.Year.extended"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__25 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__25_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__26;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "extended"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__27 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__27_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__28_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__28_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__28_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__28_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__2_value),LEAN_SCALAR_PTR_LITERAL(81, 61, 104, 127, 147, 223, 116, 59)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__28_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__27_value),LEAN_SCALAR_PTR_LITERAL(173, 52, 201, 124, 50, 137, 219, 209)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__28 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__28_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__28_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__29 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__29_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__28_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__30 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__30_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__30_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__31 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__31_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__29_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__31_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__32 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__32_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertYear(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertYear___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Std.Time.ZoneName.short"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__0 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__0_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__1;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ZoneName"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__2 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__2_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__3_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__3_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 221, 249, 71, 196, 230, 130, 14)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__3_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__5_value),LEAN_SCALAR_PTR_LITERAL(48, 208, 46, 14, 98, 17, 211, 187)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__3 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__3_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__4 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__4_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__3_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__5 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__5_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__6 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__6_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__4_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__6_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__7 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__7_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Std.Time.ZoneName.full"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__8 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__8_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__9;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__10_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__10_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 221, 249, 71, 196, 230, 130, 14)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__10_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__13_value),LEAN_SCALAR_PTR_LITERAL(227, 76, 103, 143, 218, 9, 212, 240)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__10 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__10_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__11 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__11_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__10_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__12 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__12_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__12_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__13 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__13_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__11_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__13_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__14 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__14_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZoneName(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZoneName___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Std.Time.OffsetX.hour"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__0 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__0_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__1;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "OffsetX"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__2 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__2_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hour"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__3 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__3_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__4_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__4_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__2_value),LEAN_SCALAR_PTR_LITERAL(72, 17, 42, 12, 20, 221, 211, 164)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__4_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__3_value),LEAN_SCALAR_PTR_LITERAL(94, 128, 73, 10, 93, 38, 17, 147)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__4 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__4_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__5 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__5_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__4_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__6 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__6_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__7 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__7_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__5_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__7_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__8 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__8_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Std.Time.OffsetX.hourMinute"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__9 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__9_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__10;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "hourMinute"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__11 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__11_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__12_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__12_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__2_value),LEAN_SCALAR_PTR_LITERAL(72, 17, 42, 12, 20, 221, 211, 164)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__12_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__11_value),LEAN_SCALAR_PTR_LITERAL(224, 164, 8, 144, 244, 85, 185, 49)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__12 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__12_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__12_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__13 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__13_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__12_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__14 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__14_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__14_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__15 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__15_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__13_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__15_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__16 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__16_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Std.Time.OffsetX.hourMinuteColon"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__17 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__17_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__18;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "hourMinuteColon"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__19 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__19_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__20_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__20_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__2_value),LEAN_SCALAR_PTR_LITERAL(72, 17, 42, 12, 20, 221, 211, 164)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__20_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__19_value),LEAN_SCALAR_PTR_LITERAL(41, 14, 191, 247, 70, 78, 152, 94)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__20 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__20_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__20_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__21 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__21_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__20_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__22 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__22_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__22_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__23 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__23_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__21_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__23_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__24 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__24_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Std.Time.OffsetX.hourMinuteSecond"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__25 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__25_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__26;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "hourMinuteSecond"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__27 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__27_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__28_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__28_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__28_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__28_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__2_value),LEAN_SCALAR_PTR_LITERAL(72, 17, 42, 12, 20, 221, 211, 164)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__28_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__27_value),LEAN_SCALAR_PTR_LITERAL(225, 206, 103, 171, 252, 66, 132, 235)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__28 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__28_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__28_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__29 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__29_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__28_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__30 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__30_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__30_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__31 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__31_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__29_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__31_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__32 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__32_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "Std.Time.OffsetX.hourMinuteSecondColon"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__33 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__33_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__34;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "hourMinuteSecondColon"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__35 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__35_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__36_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__36_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__36_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__36_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__36_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__2_value),LEAN_SCALAR_PTR_LITERAL(72, 17, 42, 12, 20, 221, 211, 164)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__36_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__35_value),LEAN_SCALAR_PTR_LITERAL(140, 30, 191, 40, 228, 93, 219, 98)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__36 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__36_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__36_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__37 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__37_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__36_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__38 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__38_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__38_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__39 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__39_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__37_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__39_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__40 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__40_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetX(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Std.Time.OffsetO.short"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__0 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__0_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__1;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "OffsetO"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__2 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__2_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__3_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__3_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__2_value),LEAN_SCALAR_PTR_LITERAL(67, 124, 82, 133, 197, 108, 218, 207)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__3_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__5_value),LEAN_SCALAR_PTR_LITERAL(12, 166, 178, 82, 100, 100, 15, 194)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__3 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__3_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__4 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__4_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__3_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__5 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__5_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__6 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__6_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__4_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__6_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__7 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__7_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Std.Time.OffsetO.full"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__8 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__8_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__9;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__10_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__10_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__2_value),LEAN_SCALAR_PTR_LITERAL(67, 124, 82, 133, 197, 108, 218, 207)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__10_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__13_value),LEAN_SCALAR_PTR_LITERAL(87, 208, 214, 192, 175, 181, 101, 171)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__10 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__10_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__11 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__11_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__10_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__12 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__12_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__12_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__13 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__13_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__11_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__13_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__14 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__14_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetO(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Std.Time.OffsetZ.hourMinute"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__0 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__0_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__1;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "OffsetZ"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__2 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__2_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__3_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__3_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__2_value),LEAN_SCALAR_PTR_LITERAL(165, 154, 120, 218, 15, 36, 228, 254)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__3_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__11_value),LEAN_SCALAR_PTR_LITERAL(17, 33, 135, 180, 146, 21, 133, 89)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__3 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__3_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__4 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__4_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__3_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__5 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__5_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__6 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__6_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__4_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__6_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__7 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__7_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Std.Time.OffsetZ.full"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__8 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__8_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__9;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__10_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__10_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__2_value),LEAN_SCALAR_PTR_LITERAL(165, 154, 120, 218, 15, 36, 228, 254)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__10_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__13_value),LEAN_SCALAR_PTR_LITERAL(161, 2, 237, 139, 76, 238, 101, 192)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__10 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__10_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__11 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__11_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__10_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__12 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__12_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__12_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__13 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__13_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__11_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__13_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__14 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__14_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "Std.Time.OffsetZ.hourMinuteSecondColon"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__15 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__15_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__16;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__17_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__17_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__2_value),LEAN_SCALAR_PTR_LITERAL(165, 154, 120, 218, 15, 36, 228, 254)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__17_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__35_value),LEAN_SCALAR_PTR_LITERAL(5, 26, 115, 31, 113, 82, 202, 87)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__17 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__17_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__17_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__18 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__18_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__17_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__19 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__19_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__19_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__20 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__20_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__18_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__20_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__21 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__21_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.G"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__0 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__0_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__1;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Modifier"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "G"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__3 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__3_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__4_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__4_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__4_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__3_value),LEAN_SCALAR_PTR_LITERAL(182, 140, 232, 180, 245, 222, 138, 191)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__4 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__4_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__5 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__5_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__4_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__6 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__6_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__7 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__7_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__5_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__7_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__8 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__8_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.y"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__9 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__9_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__10;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "y"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__11 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__11_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__12_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__12_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__12_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__11_value),LEAN_SCALAR_PTR_LITERAL(115, 95, 28, 131, 21, 96, 16, 178)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__12 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__12_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__12_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__13 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__13_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__12_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__14 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__14_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__14_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__15 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__15_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__13_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__15_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__16 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__16_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.u"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__17 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__17_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__18;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "u"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__19 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__19_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__20_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__20_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__20_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__19_value),LEAN_SCALAR_PTR_LITERAL(147, 80, 165, 32, 82, 240, 32, 222)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__20 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__20_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__20_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__21 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__21_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__20_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__22 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__22_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__22_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__23 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__23_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__21_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__23_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__24 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__24_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.Y"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__25 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__25_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__26;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "Y"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__27 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__27_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__28_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__28_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__28_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__28_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__28_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__27_value),LEAN_SCALAR_PTR_LITERAL(14, 155, 135, 75, 42, 253, 153, 241)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__28 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__28_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__28_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__29 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__29_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__28_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__30 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__30_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__30_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__31 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__31_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__29_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__31_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__32 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__32_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.D"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__33 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__33_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__34;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "D"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__35 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__35_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__36_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__36_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__36_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__36_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__36_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__36_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__35_value),LEAN_SCALAR_PTR_LITERAL(110, 212, 173, 37, 208, 12, 21, 131)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__36 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__36_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__36_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__37 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__37_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__36_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__38 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__38_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__38_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__39 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__39_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__37_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__39_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__40 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__40_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Std.Time.Modifier.MorL"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__41 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__41_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__42;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "MorL"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__43 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__43_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__44_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__44_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__44_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__44_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__44_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__44_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__43_value),LEAN_SCALAR_PTR_LITERAL(187, 73, 66, 86, 160, 81, 156, 182)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__44 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__44_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__44_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__45 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__45_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__44_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__46 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__46_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__46_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__47 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__47_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__45_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__47_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__48 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__48_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__50_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__50_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__50_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__50_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__50_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__50_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__50 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__50_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__51 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__51_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__52_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__52_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__52_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__52_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__52_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__52_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__51_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__52 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__52_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__53 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__53_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__54 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__54_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__54_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__55 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__55_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__56 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__56_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__57_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__57;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__58_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__58_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__58 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__58_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__58_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__59 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__59_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__60 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__60_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__60_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__61 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__61_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__62 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__62_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__63_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__63_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__63_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__63_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__62_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__63 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__63_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__63_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__64 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__64_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__65_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__65_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__65 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__65_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__65_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__66 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__66_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__67 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__67_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__67_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__68 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__68_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__68_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__69 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__69_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__66_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__69_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__70 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__70_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__64_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__70_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__71 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__71_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__61_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__71_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__72 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__72_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__59_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__72_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__73 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__73_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "dotIdent"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__74 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__74_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__75_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__75_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__75_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__75_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__75_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__75_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__74_value),LEAN_SCALAR_PTR_LITERAL(173, 139, 76, 218, 89, 59, 213, 196)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__75 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__75_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__76 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__76_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "inl"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__77 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__77_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__78_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__78;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__77_value),LEAN_SCALAR_PTR_LITERAL(86, 142, 99, 99, 156, 120, 56, 132)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__79 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__79_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__80_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__80 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__80_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__81_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "inr"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__81 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__81_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__82_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__82;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__83_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__81_value),LEAN_SCALAR_PTR_LITERAL(209, 212, 202, 104, 137, 8, 49, 108)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__83 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__83_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__84_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.d"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__84 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__84_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__85_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__85;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__86_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "d"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__86 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__86_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__87_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__87_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__87_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__87_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__87_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__87_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__87_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__86_value),LEAN_SCALAR_PTR_LITERAL(43, 177, 95, 132, 207, 75, 80, 59)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__87 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__87_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__88_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__87_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__88 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__88_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__89_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__87_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__89 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__89_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__90_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__89_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__90 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__90_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__91_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__88_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__90_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__91 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__91_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__92_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Std.Time.Modifier.Qorq"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__92 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__92_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__93_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__93;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__94_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Qorq"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__94 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__94_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__95_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__95_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__95_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__95_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__95_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__95_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__95_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__94_value),LEAN_SCALAR_PTR_LITERAL(239, 139, 79, 232, 51, 16, 131, 46)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__95 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__95_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__96_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__95_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__96 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__96_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__97_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__95_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__97 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__97_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__98_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__97_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__98 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__98_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__99_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__96_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__98_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__99 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__99_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__100_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.w"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__100 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__100_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__101_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__101;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__102_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "w"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__102 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__102_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__103_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__103_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__103_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__103_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__103_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__103_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__103_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__102_value),LEAN_SCALAR_PTR_LITERAL(109, 122, 115, 3, 58, 174, 210, 61)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__103 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__103_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__104_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__103_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__104 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__104_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__105_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__103_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__105 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__105_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__106_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__105_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__106 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__106_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__107_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__104_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__106_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__107 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__107_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__108_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.W"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__108 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__108_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__109_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__109;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__110_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "W"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__110 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__110_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__111_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__111_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__111_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__111_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__111_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__111_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__111_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__110_value),LEAN_SCALAR_PTR_LITERAL(142, 210, 249, 219, 201, 68, 141, 242)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__111 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__111_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__112_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__111_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__112 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__112_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__113_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__111_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__113 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__113_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__114_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__113_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__114 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__114_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__115_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__112_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__114_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__115 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__115_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__116_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.E"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__116 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__116_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__117_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__117;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__118_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "E"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__118 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__118_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__119_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__119_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__119_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__119_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__119_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__119_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__119_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__118_value),LEAN_SCALAR_PTR_LITERAL(221, 114, 205, 107, 57, 101, 237, 55)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__119 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__119_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__120_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__119_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__120 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__120_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__121_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__119_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__121 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__121_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__122_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__121_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__122 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__122_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__123_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__120_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__122_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__123 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__123_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__124_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Std.Time.Modifier.eorc"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__124 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__124_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__125_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__125;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__126_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "eorc"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__126 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__126_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__127_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__127_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__127_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__127_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__127_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__127_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__127_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__126_value),LEAN_SCALAR_PTR_LITERAL(158, 189, 225, 255, 240, 175, 155, 162)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__127 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__127_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__128_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__127_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__128 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__128_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__129_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__127_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__129 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__129_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__130_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__129_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__130 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__130_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__131_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__128_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__130_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__131 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__131_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__132_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.F"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__132 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__132_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__133_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__133;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__134_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "F"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__134 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__134_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__135_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__135_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__135_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__135_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__135_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__135_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__135_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__134_value),LEAN_SCALAR_PTR_LITERAL(255, 172, 252, 76, 184, 53, 176, 25)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__135 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__135_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__136_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__135_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__136 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__136_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__137_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__135_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__137 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__137_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__138_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__137_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__138 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__138_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__139_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__136_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__138_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__139 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__139_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__140_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.a"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__140 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__140_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__141_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__141;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__142_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "a"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__142 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__142_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__143_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__143_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__143_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__143_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__143_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__143_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__143_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__142_value),LEAN_SCALAR_PTR_LITERAL(36, 69, 244, 234, 150, 73, 242, 198)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__143 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__143_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__144_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__143_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__144 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__144_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__145_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__143_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__145 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__145_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__146_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__145_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__146 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__146_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__147_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__144_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__146_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__147 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__147_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__148_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.h"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__148 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__148_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__149_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__149;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__150_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__150 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__150_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__151_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__151_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__151_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__151_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__151_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__151_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__151_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__150_value),LEAN_SCALAR_PTR_LITERAL(171, 19, 0, 95, 105, 8, 122, 135)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__151 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__151_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__152_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__151_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__152 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__152_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__153_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__151_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__153 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__153_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__154_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__153_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__154 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__154_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__155_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__152_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__154_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__155 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__155_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__156_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.K"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__156 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__156_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__157_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__157;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__158_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "K"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__158 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__158_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__159_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__159_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__159_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__159_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__159_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__159_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__159_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__158_value),LEAN_SCALAR_PTR_LITERAL(175, 237, 107, 230, 188, 207, 116, 239)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__159 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__159_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__160_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__159_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__160 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__160_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__161_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__159_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__161 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__161_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__162_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__161_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__162 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__162_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__163_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__160_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__162_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__163 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__163_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__164_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.k"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__164 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__164_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__165_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__165;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__166_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "k"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__166 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__166_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__167_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__167_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__167_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__167_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__167_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__167_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__167_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__166_value),LEAN_SCALAR_PTR_LITERAL(186, 55, 92, 94, 160, 8, 215, 223)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__167 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__167_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__168_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__167_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__168 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__168_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__169_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__167_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__169 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__169_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__170_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__169_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__170 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__170_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__171_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__168_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__170_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__171 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__171_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__172_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.H"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__172 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__172_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__173_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__173;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__174_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "H"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__174 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__174_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__175_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__175_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__175_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__175_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__175_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__175_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__175_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__174_value),LEAN_SCALAR_PTR_LITERAL(202, 31, 161, 0, 128, 16, 18, 169)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__175 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__175_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__176_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__175_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__176 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__176_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__177_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__175_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__177 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__177_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__178_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__177_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__178 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__178_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__179_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__176_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__178_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__179 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__179_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__180_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.m"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__180 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__180_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__181_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__181;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__182_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "m"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__182 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__182_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__183_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__183_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__183_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__183_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__183_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__183_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__183_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__182_value),LEAN_SCALAR_PTR_LITERAL(118, 254, 173, 99, 0, 222, 89, 33)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__183 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__183_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__184_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__183_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__184 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__184_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__185_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__183_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__185 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__185_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__186_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__185_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__186 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__186_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__187_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__184_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__186_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__187 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__187_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__188_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.s"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__188 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__188_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__189_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__189;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__190_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "s"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__190 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__190_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__191_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__191_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__191_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__191_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__191_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__191_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__191_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__190_value),LEAN_SCALAR_PTR_LITERAL(80, 170, 75, 145, 176, 122, 31, 111)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__191 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__191_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__192_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__191_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__192 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__192_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__193_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__191_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__193 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__193_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__194_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__193_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__194 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__194_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__195_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__192_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__194_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__195 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__195_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__196_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.S"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__196 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__196_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__197_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__197;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__198_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "S"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__198 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__198_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__199_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__199_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__199_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__199_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__199_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__199_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__199_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__198_value),LEAN_SCALAR_PTR_LITERAL(61, 110, 227, 5, 165, 49, 182, 207)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__199 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__199_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__200_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__199_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__200 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__200_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__201_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__199_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__201 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__201_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__202_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__201_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__202 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__202_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__203_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__200_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__202_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__203 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__203_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__204_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.A"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__204 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__204_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__205_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__205;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__206_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "A"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__206 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__206_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__207_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__207_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__207_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__207_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__207_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__207_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__207_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__206_value),LEAN_SCALAR_PTR_LITERAL(254, 42, 156, 100, 183, 179, 31, 180)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__207 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__207_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__208_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__207_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__208 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__208_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__209_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__207_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__209 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__209_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__210_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__209_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__210 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__210_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__211_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__208_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__210_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__211 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__211_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__212_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.n"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__212 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__212_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__213_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__213;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__214_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "n"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__214 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__214_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__215_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__215_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__215_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__215_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__215_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__215_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__215_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__214_value),LEAN_SCALAR_PTR_LITERAL(38, 78, 251, 143, 117, 169, 85, 233)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__215 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__215_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__216_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__215_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__216 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__216_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__217_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__215_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__217 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__217_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__218_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__217_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__218 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__218_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__219_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__216_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__218_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__219 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__219_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__220_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.N"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__220 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__220_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__221_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__221;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__222_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "N"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__222 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__222_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__223_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__223_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__223_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__223_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__223_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__223_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__223_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__222_value),LEAN_SCALAR_PTR_LITERAL(139, 9, 15, 62, 231, 211, 146, 60)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__223 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__223_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__224_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__223_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__224 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__224_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__225_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__223_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__225 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__225_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__226_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__225_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__226 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__226_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__227_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__224_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__226_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__227 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__227_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__228_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.V"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__228 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__228_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__229_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__229;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__230_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "V"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__230 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__230_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__231_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__231_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__231_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__231_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__231_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__231_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__231_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__230_value),LEAN_SCALAR_PTR_LITERAL(49, 190, 37, 135, 7, 5, 128, 4)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__231 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__231_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__232_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__231_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__232 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__232_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__233_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__231_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__233 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__233_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__234_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__233_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__234 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__234_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__235_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__232_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__234_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__235 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__235_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__236_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.z"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__236 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__236_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__237_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__237;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__238_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "z"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__238 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__238_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__239_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__239_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__239_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__239_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__239_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__239_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__239_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__238_value),LEAN_SCALAR_PTR_LITERAL(181, 218, 97, 100, 129, 163, 177, 227)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__239 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__239_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__240_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__239_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__240 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__240_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__241_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__239_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__241 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__241_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__242_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__241_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__242 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__242_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__243_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__240_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__242_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__243 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__243_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__244_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.O"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__244 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__244_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__245_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__245;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__246_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "O"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__246 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__246_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__247_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__247_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__247_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__247_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__247_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__247_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__247_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__246_value),LEAN_SCALAR_PTR_LITERAL(58, 151, 205, 45, 234, 213, 167, 33)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__247 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__247_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__248_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__247_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__248 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__248_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__249_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__247_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__249 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__249_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__250_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__249_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__250 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__250_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__251_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__248_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__250_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__251 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__251_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__252_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.X"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__252 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__252_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__253_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__253;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__254_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "X"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__254 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__254_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__255_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__255_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__255_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__255_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__255_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__255_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__255_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__254_value),LEAN_SCALAR_PTR_LITERAL(26, 41, 196, 142, 13, 161, 206, 121)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__255 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__255_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__256_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__255_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__256 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__256_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__257_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__255_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__257 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__257_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__258_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__257_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__258 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__258_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__259_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__256_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__258_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__259 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__259_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__260_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.x"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__260 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__260_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__261_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__261;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__262_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__262 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__262_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__263_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__263_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__263_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__263_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__263_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__263_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__263_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__262_value),LEAN_SCALAR_PTR_LITERAL(200, 2, 62, 177, 15, 17, 219, 69)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__263 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__263_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__264_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__263_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__264 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__264_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__265_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__263_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__265 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__265_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__266_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__265_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__266 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__266_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__267_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__264_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__266_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__267 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__267_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__268_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.Z"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__268 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__268_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__269_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__269;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__270_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "Z"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__270 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__270_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__271_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__271_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__271_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__271_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__271_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__271_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__271_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__270_value),LEAN_SCALAR_PTR_LITERAL(44, 18, 171, 9, 22, 243, 82, 66)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__271 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__271_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__272_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__271_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__272 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__272_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__273_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__271_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__273 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__273_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__274_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__273_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__274 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__274_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__275_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__272_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__274_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__275 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__275_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertFormatPart___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "string"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertFormatPart___closed__0 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertFormatPart___closed__0_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertFormatPart___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertFormatPart___closed__1;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertFormatPart___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertFormatPart___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 56, 52, 137, 138, 241, 128, 175)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertFormatPart___closed__2 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertFormatPart___closed__2_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertFormatPart___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "modifier"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertFormatPart___closed__3 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertFormatPart___closed__3_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertFormatPart___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertFormatPart___closed__4;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertFormatPart___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertFormatPart___closed__3_value),LEAN_SCALAR_PTR_LITERAL(225, 238, 236, 22, 130, 68, 194, 201)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertFormatPart___closed__5 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertFormatPart___closed__5_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertFormatPart(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertFormatPart___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_syntaxNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxNat___closed__0 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxNat___closed__0_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_syntaxNat___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxNat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(227, 68, 22, 222, 47, 51, 204, 84)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxNat___closed__1 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxNat___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxNat(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxNat___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_syntaxString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxString___closed__0 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxString___closed__0_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_syntaxString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxString___closed__0_value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxString___closed__1 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxString___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxString(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxString___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__0;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Int.ofNat"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__1 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__1_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__2;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Int"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__3 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__3_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__4 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__4_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__3_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__5_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__4_value),LEAN_SCALAR_PTR_LITERAL(192, 66, 133, 102, 95, 170, 134, 92)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__5 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__5_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__6 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__6_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__5_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__7 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__7_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__7_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__8 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__8_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__6_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__8_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__9 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__9_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Int.negSucc"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__10 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__10_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__11;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "negSucc"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__12 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__12_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__3_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__13_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__12_value),LEAN_SCALAR_PTR_LITERAL(181, 236, 205, 0, 179, 53, 99, 201)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__13 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__13_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__13_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__14 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__14_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__13_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__15 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__15_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__15_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__16 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__16_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__14_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__16_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__17 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__17_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxInt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxInt___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "Std.Time.Internal.Bounded.LE.ofNatWrapping"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__0 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__0_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__1;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Internal"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__2 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__2_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Bounded"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__3 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__3_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LE"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__4 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__4_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "ofNatWrapping"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__5 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__5_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__6_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__6_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__2_value),LEAN_SCALAR_PTR_LITERAL(113, 45, 195, 84, 32, 84, 134, 39)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__6_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__6_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__3_value),LEAN_SCALAR_PTR_LITERAL(172, 131, 129, 250, 206, 85, 214, 6)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__6_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__6_value_aux_3),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__4_value),LEAN_SCALAR_PTR_LITERAL(155, 200, 6, 67, 20, 25, 4, 138)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__6_value_aux_4),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__5_value),LEAN_SCALAR_PTR_LITERAL(108, 206, 216, 211, 87, 12, 88, 244)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__6 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__6_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__7 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__7_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__7_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__8 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__8_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "byTactic"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__9 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__9_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__10_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__10_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__10_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__9_value),LEAN_SCALAR_PTR_LITERAL(187, 150, 238, 148, 228, 221, 116, 224)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__10 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__10_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "by"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__11 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__11_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__12 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__12_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__13 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__13_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__14_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__14_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__12_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__14_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__13_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__14 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__14_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__15 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__15_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__16_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__16_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__12_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__16_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__15_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__16 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__16_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "decide"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__17 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__17_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__18_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__18_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__12_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__18_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__17_value),LEAN_SCALAR_PTR_LITERAL(53, 158, 1, 232, 101, 200, 191, 197)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__18 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__18_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__19 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__19_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__20_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__20_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__12_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__20_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__19_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__20 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__20_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__21;
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxBounded(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_syntaxVal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Std.Time.Internal.UnitVal.ofInt"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxVal___closed__0 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxVal___closed__0_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_syntaxVal___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxVal___closed__1;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_syntaxVal___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "UnitVal"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxVal___closed__2 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxVal___closed__2_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_syntaxVal___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofInt"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxVal___closed__3 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxVal___closed__3_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_syntaxVal___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_syntaxVal___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxVal___closed__4_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_syntaxVal___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxVal___closed__4_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__2_value),LEAN_SCALAR_PTR_LITERAL(113, 45, 195, 84, 32, 84, 134, 39)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_syntaxVal___closed__4_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxVal___closed__4_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxVal___closed__2_value),LEAN_SCALAR_PTR_LITERAL(245, 149, 70, 30, 194, 59, 16, 80)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_syntaxVal___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxVal___closed__4_value_aux_3),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxVal___closed__3_value),LEAN_SCALAR_PTR_LITERAL(234, 59, 78, 118, 124, 253, 180, 45)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxVal___closed__4 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxVal___closed__4_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_syntaxVal___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxVal___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxVal___closed__5 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxVal___closed__5_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_syntaxVal___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxVal___closed__4_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxVal___closed__6 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxVal___closed__6_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_syntaxVal___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxVal___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxVal___closed__7 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxVal___closed__7_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_syntaxVal___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxVal___closed__5_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxVal___closed__7_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxVal___closed__8 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxVal___closed__8_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxVal(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxVal___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Std.Time.TimeZone.Offset.ofSeconds"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffset___closed__0 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffset___closed__0_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertOffset___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffset___closed__1;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertOffset___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "TimeZone"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffset___closed__2 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffset___closed__2_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertOffset___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Offset"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffset___closed__3 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffset___closed__3_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertOffset___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "ofSeconds"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffset___closed__4 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffset___closed__4_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffset___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffset___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffset___closed__5_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffset___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffset___closed__5_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffset___closed__2_value),LEAN_SCALAR_PTR_LITERAL(123, 220, 54, 93, 124, 163, 52, 156)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffset___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffset___closed__5_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffset___closed__3_value),LEAN_SCALAR_PTR_LITERAL(167, 32, 243, 92, 92, 213, 85, 25)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffset___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffset___closed__5_value_aux_3),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffset___closed__4_value),LEAN_SCALAR_PTR_LITERAL(220, 173, 173, 169, 141, 114, 200, 158)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffset___closed__5 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffset___closed__5_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffset___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffset___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffset___closed__6 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffset___closed__6_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffset___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffset___closed__5_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffset___closed__7 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffset___closed__7_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffset___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffset___closed__7_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffset___closed__8 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffset___closed__8_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertOffset___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffset___closed__6_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffset___closed__8_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffset___closed__9 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffset___closed__9_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffset___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Std.Time.TimeZone.mk"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__0 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__0_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__1;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__2_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__2_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffset___closed__2_value),LEAN_SCALAR_PTR_LITERAL(123, 220, 54, 93, 124, 163, 52, 156)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__2_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__8_value),LEAN_SCALAR_PTR_LITERAL(159, 131, 60, 228, 243, 16, 51, 226)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__2 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__2_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__2_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__3 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__3_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__2_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__4 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__4_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__5 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__5_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__3_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__5_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__6 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__6_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__7 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__7_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__8;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__7_value),LEAN_SCALAR_PTR_LITERAL(160, 214, 196, 140, 104, 187, 164, 111)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__9 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__9_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__10 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__10_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__10_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__11_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__7_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__11 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__11_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__11_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__12 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__12_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__12_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__13 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__13_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertTimezone(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertTimezone___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertPlainDate___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Std.Time.PlainDate.ofYearMonthDayClip"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertPlainDate___closed__0 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertPlainDate___closed__0_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertPlainDate___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertPlainDate___closed__1;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertPlainDate___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "PlainDate"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertPlainDate___closed__2 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertPlainDate___closed__2_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertPlainDate___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "ofYearMonthDayClip"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertPlainDate___closed__3 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertPlainDate___closed__3_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertPlainDate___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertPlainDate___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertPlainDate___closed__4_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertPlainDate___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertPlainDate___closed__4_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertPlainDate___closed__2_value),LEAN_SCALAR_PTR_LITERAL(15, 218, 205, 117, 186, 101, 64, 32)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertPlainDate___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertPlainDate___closed__4_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertPlainDate___closed__3_value),LEAN_SCALAR_PTR_LITERAL(177, 3, 2, 67, 252, 152, 4, 161)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertPlainDate___closed__4 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertPlainDate___closed__4_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertPlainDate___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertPlainDate___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertPlainDate___closed__5 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertPlainDate___closed__5_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertPlainDate___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertPlainDate___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertPlainDate___closed__6 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertPlainDate___closed__6_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertPlainDate(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertPlainDate___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertPlainTime___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Std.Time.PlainTime.mk"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertPlainTime___closed__0 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertPlainTime___closed__0_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertPlainTime___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertPlainTime___closed__1;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertPlainTime___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "PlainTime"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertPlainTime___closed__2 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertPlainTime___closed__2_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertPlainTime___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertPlainTime___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertPlainTime___closed__3_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertPlainTime___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertPlainTime___closed__3_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertPlainTime___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 230, 186, 32, 252, 226, 250, 0)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertPlainTime___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertPlainTime___closed__3_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 160, 32, 2, 118, 10, 124, 19)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertPlainTime___closed__3 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertPlainTime___closed__3_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertPlainTime___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertPlainTime___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertPlainTime___closed__4 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertPlainTime___closed__4_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertPlainTime___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertPlainTime___closed__3_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertPlainTime___closed__5 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertPlainTime___closed__5_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertPlainTime___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertPlainTime___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertPlainTime___closed__6 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertPlainTime___closed__6_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertPlainTime___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertPlainTime___closed__4_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertPlainTime___closed__6_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertPlainTime___closed__7 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertPlainTime___closed__7_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertPlainTime(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertPlainTime___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Std.Time.PlainDateTime.mk"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime___closed__0 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime___closed__0_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime___closed__1;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "PlainDateTime"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime___closed__2 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime___closed__2_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime___closed__3_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime___closed__3_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime___closed__2_value),LEAN_SCALAR_PTR_LITERAL(244, 181, 115, 111, 151, 225, 244, 191)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime___closed__3_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__8_value),LEAN_SCALAR_PTR_LITERAL(92, 55, 41, 90, 210, 196, 100, 220)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime___closed__3 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime___closed__3_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime___closed__4 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime___closed__4_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime___closed__3_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime___closed__5 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime___closed__5_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime___closed__6 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime___closed__6_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime___closed__4_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime___closed__6_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime___closed__7 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime___closed__7_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Std.Time.DateTime.ofPlainDateTime"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__0 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__0_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__1;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "DateTime"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__2 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__2_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "ofPlainDateTime"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__3 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__3_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__4_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__4_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__2_value),LEAN_SCALAR_PTR_LITERAL(105, 115, 26, 239, 209, 16, 240, 145)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__4_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__3_value),LEAN_SCALAR_PTR_LITERAL(81, 182, 24, 109, 104, 29, 3, 191)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__4 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__4_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__5 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__5_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__6 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__6_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "Std.Time.TimeZone.ZoneRules.ofTimeZone"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__7 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__7_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__8;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "ZoneRules"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__9 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__9_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "ofTimeZone"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__10 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__10_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__11_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__11_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffset___closed__2_value),LEAN_SCALAR_PTR_LITERAL(123, 220, 54, 93, 124, 163, 52, 156)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__11_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__11_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__9_value),LEAN_SCALAR_PTR_LITERAL(195, 137, 30, 162, 40, 87, 69, 227)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__11_value_aux_3),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__10_value),LEAN_SCALAR_PTR_LITERAL(63, 246, 142, 47, 38, 113, 110, 12)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__11 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__11_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__11_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__12 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__12_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__12_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__13 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__13_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "<$>"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__14 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__14_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Database"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__15 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__15_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "defaultGetZoneRules"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__16 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__16_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__17_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__17_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__15_value),LEAN_SCALAR_PTR_LITERAL(52, 29, 11, 135, 198, 98, 142, 215)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__17_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__16_value),LEAN_SCALAR_PTR_LITERAL(195, 204, 158, 115, 111, 241, 211, 242)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__17 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__17_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "term_<$>_"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__18 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__18_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__18_value),LEAN_SCALAR_PTR_LITERAL(128, 74, 67, 119, 243, 145, 72, 28)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__19 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__19_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Std.Time.Database.defaultGetZoneRules"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__20 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__20_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__21;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__17_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__22 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__22_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__22_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__23 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__23_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertDateTime(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertDateTime___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Time_termZoned_x28___x29___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "termZoned(_)"};
static const lean_object* l_Std_Time_termZoned_x28___x29___closed__0 = (const lean_object*)&l_Std_Time_termZoned_x28___x29___closed__0_value;
static const lean_ctor_object l_Std_Time_termZoned_x28___x29___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Time_termZoned_x28___x29___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_termZoned_x28___x29___closed__1_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l_Std_Time_termZoned_x28___x29___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_termZoned_x28___x29___closed__1_value_aux_1),((lean_object*)&l_Std_Time_termZoned_x28___x29___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 93, 126, 244, 143, 80, 158, 136)}};
static const lean_object* l_Std_Time_termZoned_x28___x29___closed__1 = (const lean_object*)&l_Std_Time_termZoned_x28___x29___closed__1_value;
static const lean_string_object l_Std_Time_termZoned_x28___x29___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Std_Time_termZoned_x28___x29___closed__2 = (const lean_object*)&l_Std_Time_termZoned_x28___x29___closed__2_value;
static const lean_ctor_object l_Std_Time_termZoned_x28___x29___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_termZoned_x28___x29___closed__2_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Std_Time_termZoned_x28___x29___closed__3 = (const lean_object*)&l_Std_Time_termZoned_x28___x29___closed__3_value;
static const lean_string_object l_Std_Time_termZoned_x28___x29___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "zoned("};
static const lean_object* l_Std_Time_termZoned_x28___x29___closed__4 = (const lean_object*)&l_Std_Time_termZoned_x28___x29___closed__4_value;
static const lean_ctor_object l_Std_Time_termZoned_x28___x29___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_termZoned_x28___x29___closed__4_value)}};
static const lean_object* l_Std_Time_termZoned_x28___x29___closed__5 = (const lean_object*)&l_Std_Time_termZoned_x28___x29___closed__5_value;
static const lean_ctor_object l_Std_Time_termZoned_x28___x29___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_syntaxString___closed__1_value)}};
static const lean_object* l_Std_Time_termZoned_x28___x29___closed__6 = (const lean_object*)&l_Std_Time_termZoned_x28___x29___closed__6_value;
static const lean_ctor_object l_Std_Time_termZoned_x28___x29___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Time_termZoned_x28___x29___closed__3_value),((lean_object*)&l_Std_Time_termZoned_x28___x29___closed__5_value),((lean_object*)&l_Std_Time_termZoned_x28___x29___closed__6_value)}};
static const lean_object* l_Std_Time_termZoned_x28___x29___closed__7 = (const lean_object*)&l_Std_Time_termZoned_x28___x29___closed__7_value;
static const lean_ctor_object l_Std_Time_termZoned_x28___x29___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__80_value)}};
static const lean_object* l_Std_Time_termZoned_x28___x29___closed__8 = (const lean_object*)&l_Std_Time_termZoned_x28___x29___closed__8_value;
static const lean_ctor_object l_Std_Time_termZoned_x28___x29___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Time_termZoned_x28___x29___closed__3_value),((lean_object*)&l_Std_Time_termZoned_x28___x29___closed__7_value),((lean_object*)&l_Std_Time_termZoned_x28___x29___closed__8_value)}};
static const lean_object* l_Std_Time_termZoned_x28___x29___closed__9 = (const lean_object*)&l_Std_Time_termZoned_x28___x29___closed__9_value;
static const lean_ctor_object l_Std_Time_termZoned_x28___x29___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_termZoned_x28___x29___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Std_Time_termZoned_x28___x29___closed__9_value)}};
static const lean_object* l_Std_Time_termZoned_x28___x29___closed__10 = (const lean_object*)&l_Std_Time_termZoned_x28___x29___closed__10_value;
LEAN_EXPORT const lean_object* l_Std_Time_termZoned_x28___x29 = (const lean_object*)&l_Std_Time_termZoned_x28___x29___closed__10_value;
static const lean_string_object l_Std_Time_termZoned_x28___x2c___x29___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "termZoned(_,_)"};
static const lean_object* l_Std_Time_termZoned_x28___x2c___x29___closed__0 = (const lean_object*)&l_Std_Time_termZoned_x28___x2c___x29___closed__0_value;
static const lean_ctor_object l_Std_Time_termZoned_x28___x2c___x29___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Time_termZoned_x28___x2c___x29___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_termZoned_x28___x2c___x29___closed__1_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l_Std_Time_termZoned_x28___x2c___x29___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_termZoned_x28___x2c___x29___closed__1_value_aux_1),((lean_object*)&l_Std_Time_termZoned_x28___x2c___x29___closed__0_value),LEAN_SCALAR_PTR_LITERAL(113, 198, 165, 221, 166, 80, 106, 244)}};
static const lean_object* l_Std_Time_termZoned_x28___x2c___x29___closed__1 = (const lean_object*)&l_Std_Time_termZoned_x28___x2c___x29___closed__1_value;
static const lean_string_object l_Std_Time_termZoned_x28___x2c___x29___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Std_Time_termZoned_x28___x2c___x29___closed__2 = (const lean_object*)&l_Std_Time_termZoned_x28___x2c___x29___closed__2_value;
static const lean_ctor_object l_Std_Time_termZoned_x28___x2c___x29___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_termZoned_x28___x2c___x29___closed__2_value)}};
static const lean_object* l_Std_Time_termZoned_x28___x2c___x29___closed__3 = (const lean_object*)&l_Std_Time_termZoned_x28___x2c___x29___closed__3_value;
static const lean_ctor_object l_Std_Time_termZoned_x28___x2c___x29___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Time_termZoned_x28___x29___closed__3_value),((lean_object*)&l_Std_Time_termZoned_x28___x29___closed__7_value),((lean_object*)&l_Std_Time_termZoned_x28___x2c___x29___closed__3_value)}};
static const lean_object* l_Std_Time_termZoned_x28___x2c___x29___closed__4 = (const lean_object*)&l_Std_Time_termZoned_x28___x2c___x29___closed__4_value;
static const lean_string_object l_Std_Time_termZoned_x28___x2c___x29___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Std_Time_termZoned_x28___x2c___x29___closed__5 = (const lean_object*)&l_Std_Time_termZoned_x28___x2c___x29___closed__5_value;
static const lean_ctor_object l_Std_Time_termZoned_x28___x2c___x29___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_termZoned_x28___x2c___x29___closed__5_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Std_Time_termZoned_x28___x2c___x29___closed__6 = (const lean_object*)&l_Std_Time_termZoned_x28___x2c___x29___closed__6_value;
static const lean_ctor_object l_Std_Time_termZoned_x28___x2c___x29___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Std_Time_termZoned_x28___x2c___x29___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Time_termZoned_x28___x2c___x29___closed__7 = (const lean_object*)&l_Std_Time_termZoned_x28___x2c___x29___closed__7_value;
static const lean_ctor_object l_Std_Time_termZoned_x28___x2c___x29___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Time_termZoned_x28___x29___closed__3_value),((lean_object*)&l_Std_Time_termZoned_x28___x2c___x29___closed__4_value),((lean_object*)&l_Std_Time_termZoned_x28___x2c___x29___closed__7_value)}};
static const lean_object* l_Std_Time_termZoned_x28___x2c___x29___closed__8 = (const lean_object*)&l_Std_Time_termZoned_x28___x2c___x29___closed__8_value;
static const lean_ctor_object l_Std_Time_termZoned_x28___x2c___x29___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Time_termZoned_x28___x29___closed__3_value),((lean_object*)&l_Std_Time_termZoned_x28___x2c___x29___closed__8_value),((lean_object*)&l_Std_Time_termZoned_x28___x29___closed__8_value)}};
static const lean_object* l_Std_Time_termZoned_x28___x2c___x29___closed__9 = (const lean_object*)&l_Std_Time_termZoned_x28___x2c___x29___closed__9_value;
static const lean_ctor_object l_Std_Time_termZoned_x28___x2c___x29___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_termZoned_x28___x2c___x29___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Std_Time_termZoned_x28___x2c___x29___closed__9_value)}};
static const lean_object* l_Std_Time_termZoned_x28___x2c___x29___closed__10 = (const lean_object*)&l_Std_Time_termZoned_x28___x2c___x29___closed__10_value;
LEAN_EXPORT const lean_object* l_Std_Time_termZoned_x28___x2c___x29 = (const lean_object*)&l_Std_Time_termZoned_x28___x2c___x29___closed__10_value;
static const lean_string_object l_Std_Time_termDatetime_x28___x29___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "termDatetime(_)"};
static const lean_object* l_Std_Time_termDatetime_x28___x29___closed__0 = (const lean_object*)&l_Std_Time_termDatetime_x28___x29___closed__0_value;
static const lean_ctor_object l_Std_Time_termDatetime_x28___x29___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Time_termDatetime_x28___x29___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_termDatetime_x28___x29___closed__1_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l_Std_Time_termDatetime_x28___x29___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_termDatetime_x28___x29___closed__1_value_aux_1),((lean_object*)&l_Std_Time_termDatetime_x28___x29___closed__0_value),LEAN_SCALAR_PTR_LITERAL(242, 97, 38, 153, 227, 76, 238, 149)}};
static const lean_object* l_Std_Time_termDatetime_x28___x29___closed__1 = (const lean_object*)&l_Std_Time_termDatetime_x28___x29___closed__1_value;
static const lean_string_object l_Std_Time_termDatetime_x28___x29___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "datetime("};
static const lean_object* l_Std_Time_termDatetime_x28___x29___closed__2 = (const lean_object*)&l_Std_Time_termDatetime_x28___x29___closed__2_value;
static const lean_ctor_object l_Std_Time_termDatetime_x28___x29___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_termDatetime_x28___x29___closed__2_value)}};
static const lean_object* l_Std_Time_termDatetime_x28___x29___closed__3 = (const lean_object*)&l_Std_Time_termDatetime_x28___x29___closed__3_value;
static const lean_ctor_object l_Std_Time_termDatetime_x28___x29___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Time_termZoned_x28___x29___closed__3_value),((lean_object*)&l_Std_Time_termDatetime_x28___x29___closed__3_value),((lean_object*)&l_Std_Time_termZoned_x28___x29___closed__6_value)}};
static const lean_object* l_Std_Time_termDatetime_x28___x29___closed__4 = (const lean_object*)&l_Std_Time_termDatetime_x28___x29___closed__4_value;
static const lean_ctor_object l_Std_Time_termDatetime_x28___x29___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Time_termZoned_x28___x29___closed__3_value),((lean_object*)&l_Std_Time_termDatetime_x28___x29___closed__4_value),((lean_object*)&l_Std_Time_termZoned_x28___x29___closed__8_value)}};
static const lean_object* l_Std_Time_termDatetime_x28___x29___closed__5 = (const lean_object*)&l_Std_Time_termDatetime_x28___x29___closed__5_value;
static const lean_ctor_object l_Std_Time_termDatetime_x28___x29___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_termDatetime_x28___x29___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Std_Time_termDatetime_x28___x29___closed__5_value)}};
static const lean_object* l_Std_Time_termDatetime_x28___x29___closed__6 = (const lean_object*)&l_Std_Time_termDatetime_x28___x29___closed__6_value;
LEAN_EXPORT const lean_object* l_Std_Time_termDatetime_x28___x29 = (const lean_object*)&l_Std_Time_termDatetime_x28___x29___closed__6_value;
static const lean_string_object l_Std_Time_termDate_x28___x29___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "termDate(_)"};
static const lean_object* l_Std_Time_termDate_x28___x29___closed__0 = (const lean_object*)&l_Std_Time_termDate_x28___x29___closed__0_value;
static const lean_ctor_object l_Std_Time_termDate_x28___x29___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Time_termDate_x28___x29___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_termDate_x28___x29___closed__1_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l_Std_Time_termDate_x28___x29___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_termDate_x28___x29___closed__1_value_aux_1),((lean_object*)&l_Std_Time_termDate_x28___x29___closed__0_value),LEAN_SCALAR_PTR_LITERAL(158, 19, 6, 45, 102, 199, 247, 82)}};
static const lean_object* l_Std_Time_termDate_x28___x29___closed__1 = (const lean_object*)&l_Std_Time_termDate_x28___x29___closed__1_value;
static const lean_string_object l_Std_Time_termDate_x28___x29___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "date("};
static const lean_object* l_Std_Time_termDate_x28___x29___closed__2 = (const lean_object*)&l_Std_Time_termDate_x28___x29___closed__2_value;
static const lean_ctor_object l_Std_Time_termDate_x28___x29___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_termDate_x28___x29___closed__2_value)}};
static const lean_object* l_Std_Time_termDate_x28___x29___closed__3 = (const lean_object*)&l_Std_Time_termDate_x28___x29___closed__3_value;
static const lean_ctor_object l_Std_Time_termDate_x28___x29___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Time_termZoned_x28___x29___closed__3_value),((lean_object*)&l_Std_Time_termDate_x28___x29___closed__3_value),((lean_object*)&l_Std_Time_termZoned_x28___x29___closed__6_value)}};
static const lean_object* l_Std_Time_termDate_x28___x29___closed__4 = (const lean_object*)&l_Std_Time_termDate_x28___x29___closed__4_value;
static const lean_ctor_object l_Std_Time_termDate_x28___x29___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Time_termZoned_x28___x29___closed__3_value),((lean_object*)&l_Std_Time_termDate_x28___x29___closed__4_value),((lean_object*)&l_Std_Time_termZoned_x28___x29___closed__8_value)}};
static const lean_object* l_Std_Time_termDate_x28___x29___closed__5 = (const lean_object*)&l_Std_Time_termDate_x28___x29___closed__5_value;
static const lean_ctor_object l_Std_Time_termDate_x28___x29___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_termDate_x28___x29___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Std_Time_termDate_x28___x29___closed__5_value)}};
static const lean_object* l_Std_Time_termDate_x28___x29___closed__6 = (const lean_object*)&l_Std_Time_termDate_x28___x29___closed__6_value;
LEAN_EXPORT const lean_object* l_Std_Time_termDate_x28___x29 = (const lean_object*)&l_Std_Time_termDate_x28___x29___closed__6_value;
static const lean_string_object l_Std_Time_termTime_x28___x29___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "termTime(_)"};
static const lean_object* l_Std_Time_termTime_x28___x29___closed__0 = (const lean_object*)&l_Std_Time_termTime_x28___x29___closed__0_value;
static const lean_ctor_object l_Std_Time_termTime_x28___x29___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Time_termTime_x28___x29___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_termTime_x28___x29___closed__1_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l_Std_Time_termTime_x28___x29___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_termTime_x28___x29___closed__1_value_aux_1),((lean_object*)&l_Std_Time_termTime_x28___x29___closed__0_value),LEAN_SCALAR_PTR_LITERAL(85, 133, 123, 15, 138, 216, 108, 236)}};
static const lean_object* l_Std_Time_termTime_x28___x29___closed__1 = (const lean_object*)&l_Std_Time_termTime_x28___x29___closed__1_value;
static const lean_string_object l_Std_Time_termTime_x28___x29___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "time("};
static const lean_object* l_Std_Time_termTime_x28___x29___closed__2 = (const lean_object*)&l_Std_Time_termTime_x28___x29___closed__2_value;
static const lean_ctor_object l_Std_Time_termTime_x28___x29___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_termTime_x28___x29___closed__2_value)}};
static const lean_object* l_Std_Time_termTime_x28___x29___closed__3 = (const lean_object*)&l_Std_Time_termTime_x28___x29___closed__3_value;
static const lean_ctor_object l_Std_Time_termTime_x28___x29___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Time_termZoned_x28___x29___closed__3_value),((lean_object*)&l_Std_Time_termTime_x28___x29___closed__3_value),((lean_object*)&l_Std_Time_termZoned_x28___x29___closed__6_value)}};
static const lean_object* l_Std_Time_termTime_x28___x29___closed__4 = (const lean_object*)&l_Std_Time_termTime_x28___x29___closed__4_value;
static const lean_ctor_object l_Std_Time_termTime_x28___x29___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Time_termZoned_x28___x29___closed__3_value),((lean_object*)&l_Std_Time_termTime_x28___x29___closed__4_value),((lean_object*)&l_Std_Time_termZoned_x28___x29___closed__8_value)}};
static const lean_object* l_Std_Time_termTime_x28___x29___closed__5 = (const lean_object*)&l_Std_Time_termTime_x28___x29___closed__5_value;
static const lean_ctor_object l_Std_Time_termTime_x28___x29___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_termTime_x28___x29___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Std_Time_termTime_x28___x29___closed__5_value)}};
static const lean_object* l_Std_Time_termTime_x28___x29___closed__6 = (const lean_object*)&l_Std_Time_termTime_x28___x29___closed__6_value;
LEAN_EXPORT const lean_object* l_Std_Time_termTime_x28___x29 = (const lean_object*)&l_Std_Time_termTime_x28___x29___closed__6_value;
static const lean_string_object l_Std_Time_termOffset_x28___x29___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "termOffset(_)"};
static const lean_object* l_Std_Time_termOffset_x28___x29___closed__0 = (const lean_object*)&l_Std_Time_termOffset_x28___x29___closed__0_value;
static const lean_ctor_object l_Std_Time_termOffset_x28___x29___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Time_termOffset_x28___x29___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_termOffset_x28___x29___closed__1_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l_Std_Time_termOffset_x28___x29___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_termOffset_x28___x29___closed__1_value_aux_1),((lean_object*)&l_Std_Time_termOffset_x28___x29___closed__0_value),LEAN_SCALAR_PTR_LITERAL(11, 188, 135, 138, 129, 64, 205, 196)}};
static const lean_object* l_Std_Time_termOffset_x28___x29___closed__1 = (const lean_object*)&l_Std_Time_termOffset_x28___x29___closed__1_value;
static const lean_string_object l_Std_Time_termOffset_x28___x29___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "offset("};
static const lean_object* l_Std_Time_termOffset_x28___x29___closed__2 = (const lean_object*)&l_Std_Time_termOffset_x28___x29___closed__2_value;
static const lean_ctor_object l_Std_Time_termOffset_x28___x29___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_termOffset_x28___x29___closed__2_value)}};
static const lean_object* l_Std_Time_termOffset_x28___x29___closed__3 = (const lean_object*)&l_Std_Time_termOffset_x28___x29___closed__3_value;
static const lean_ctor_object l_Std_Time_termOffset_x28___x29___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Time_termZoned_x28___x29___closed__3_value),((lean_object*)&l_Std_Time_termOffset_x28___x29___closed__3_value),((lean_object*)&l_Std_Time_termZoned_x28___x29___closed__6_value)}};
static const lean_object* l_Std_Time_termOffset_x28___x29___closed__4 = (const lean_object*)&l_Std_Time_termOffset_x28___x29___closed__4_value;
static const lean_ctor_object l_Std_Time_termOffset_x28___x29___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Time_termZoned_x28___x29___closed__3_value),((lean_object*)&l_Std_Time_termOffset_x28___x29___closed__4_value),((lean_object*)&l_Std_Time_termZoned_x28___x29___closed__8_value)}};
static const lean_object* l_Std_Time_termOffset_x28___x29___closed__5 = (const lean_object*)&l_Std_Time_termOffset_x28___x29___closed__5_value;
static const lean_ctor_object l_Std_Time_termOffset_x28___x29___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_termOffset_x28___x29___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Std_Time_termOffset_x28___x29___closed__5_value)}};
static const lean_object* l_Std_Time_termOffset_x28___x29___closed__6 = (const lean_object*)&l_Std_Time_termOffset_x28___x29___closed__6_value;
LEAN_EXPORT const lean_object* l_Std_Time_termOffset_x28___x29 = (const lean_object*)&l_Std_Time_termOffset_x28___x29___closed__6_value;
static const lean_string_object l_Std_Time_termTimezone_x28___x29___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "termTimezone(_)"};
static const lean_object* l_Std_Time_termTimezone_x28___x29___closed__0 = (const lean_object*)&l_Std_Time_termTimezone_x28___x29___closed__0_value;
static const lean_ctor_object l_Std_Time_termTimezone_x28___x29___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Time_termTimezone_x28___x29___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_termTimezone_x28___x29___closed__1_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l_Std_Time_termTimezone_x28___x29___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_termTimezone_x28___x29___closed__1_value_aux_1),((lean_object*)&l_Std_Time_termTimezone_x28___x29___closed__0_value),LEAN_SCALAR_PTR_LITERAL(123, 93, 67, 49, 253, 69, 174, 185)}};
static const lean_object* l_Std_Time_termTimezone_x28___x29___closed__1 = (const lean_object*)&l_Std_Time_termTimezone_x28___x29___closed__1_value;
static const lean_string_object l_Std_Time_termTimezone_x28___x29___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "timezone("};
static const lean_object* l_Std_Time_termTimezone_x28___x29___closed__2 = (const lean_object*)&l_Std_Time_termTimezone_x28___x29___closed__2_value;
static const lean_ctor_object l_Std_Time_termTimezone_x28___x29___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_termTimezone_x28___x29___closed__2_value)}};
static const lean_object* l_Std_Time_termTimezone_x28___x29___closed__3 = (const lean_object*)&l_Std_Time_termTimezone_x28___x29___closed__3_value;
static const lean_ctor_object l_Std_Time_termTimezone_x28___x29___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Time_termZoned_x28___x29___closed__3_value),((lean_object*)&l_Std_Time_termTimezone_x28___x29___closed__3_value),((lean_object*)&l_Std_Time_termZoned_x28___x29___closed__6_value)}};
static const lean_object* l_Std_Time_termTimezone_x28___x29___closed__4 = (const lean_object*)&l_Std_Time_termTimezone_x28___x29___closed__4_value;
static const lean_ctor_object l_Std_Time_termTimezone_x28___x29___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Time_termZoned_x28___x29___closed__3_value),((lean_object*)&l_Std_Time_termTimezone_x28___x29___closed__4_value),((lean_object*)&l_Std_Time_termZoned_x28___x29___closed__8_value)}};
static const lean_object* l_Std_Time_termTimezone_x28___x29___closed__5 = (const lean_object*)&l_Std_Time_termTimezone_x28___x29___closed__5_value;
static const lean_ctor_object l_Std_Time_termTimezone_x28___x29___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_termTimezone_x28___x29___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Std_Time_termTimezone_x28___x29___closed__5_value)}};
static const lean_object* l_Std_Time_termTimezone_x28___x29___closed__6 = (const lean_object*)&l_Std_Time_termTimezone_x28___x29___closed__6_value;
LEAN_EXPORT const lean_object* l_Std_Time_termTimezone_x28___x29 = (const lean_object*)&l_Std_Time_termTimezone_x28___x29___closed__6_value;
static const lean_string_object l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termZoned_x28___x29__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "error: "};
static const lean_object* l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termZoned_x28___x29__1___closed__0 = (const lean_object*)&l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termZoned_x28___x29__1___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termZoned_x28___x29__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termZoned_x28___x29__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termZoned_x28___x2c___x29__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termZoned_x28___x2c___x29__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termDatetime_x28___x29__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termDatetime_x28___x29__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termDate_x28___x29__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termDate_x28___x29__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termTime_x28___x29__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termTime_x28___x29__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termOffset_x28___x29__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termOffset_x28___x29__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termTimezone_x28___x29__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termTimezone_x28___x29__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertText___closed__1(void){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertText___closed__0));
v___x_3_ = l_String_toRawSubstring_x27(v___x_2_);
return v___x_3_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertText___closed__12(void){
_start:
{
lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_25_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertText___closed__11));
v___x_26_ = l_String_toRawSubstring_x27(v___x_25_);
return v___x_26_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertText___closed__20(void){
_start:
{
lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_45_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertText___closed__19));
v___x_46_ = l_String_toRawSubstring_x27(v___x_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertText(uint8_t v_x_64_, lean_object* v_a_65_, lean_object* v_a_66_){
_start:
{
switch(v_x_64_)
{
case 0:
{
lean_object* v_quotContext_67_; lean_object* v_currMacroScope_68_; lean_object* v_ref_69_; uint8_t v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v_quotContext_67_ = lean_ctor_get(v_a_65_, 1);
v_currMacroScope_68_ = lean_ctor_get(v_a_65_, 2);
v_ref_69_ = lean_ctor_get(v_a_65_, 5);
v___x_70_ = 0;
v___x_71_ = l_Lean_SourceInfo_fromRef(v_ref_69_, v___x_70_);
v___x_72_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__1, &l___private_Std_Time_Notation_0__Std_Time_convertText___closed__1_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertText___closed__1);
v___x_73_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertText___closed__6));
lean_inc(v_currMacroScope_68_);
lean_inc(v_quotContext_67_);
v___x_74_ = l_Lean_addMacroScope(v_quotContext_67_, v___x_73_, v_currMacroScope_68_);
v___x_75_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertText___closed__10));
v___x_76_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_76_, 0, v___x_71_);
lean_ctor_set(v___x_76_, 1, v___x_72_);
lean_ctor_set(v___x_76_, 2, v___x_74_);
lean_ctor_set(v___x_76_, 3, v___x_75_);
v___x_77_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_77_, 0, v___x_76_);
lean_ctor_set(v___x_77_, 1, v_a_66_);
return v___x_77_;
}
case 1:
{
lean_object* v_quotContext_78_; lean_object* v_currMacroScope_79_; lean_object* v_ref_80_; uint8_t v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v_quotContext_78_ = lean_ctor_get(v_a_65_, 1);
v_currMacroScope_79_ = lean_ctor_get(v_a_65_, 2);
v_ref_80_ = lean_ctor_get(v_a_65_, 5);
v___x_81_ = 0;
v___x_82_ = l_Lean_SourceInfo_fromRef(v_ref_80_, v___x_81_);
v___x_83_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__12, &l___private_Std_Time_Notation_0__Std_Time_convertText___closed__12_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertText___closed__12);
v___x_84_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertText___closed__14));
lean_inc(v_currMacroScope_79_);
lean_inc(v_quotContext_78_);
v___x_85_ = l_Lean_addMacroScope(v_quotContext_78_, v___x_84_, v_currMacroScope_79_);
v___x_86_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertText___closed__18));
v___x_87_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_87_, 0, v___x_82_);
lean_ctor_set(v___x_87_, 1, v___x_83_);
lean_ctor_set(v___x_87_, 2, v___x_85_);
lean_ctor_set(v___x_87_, 3, v___x_86_);
v___x_88_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_88_, 0, v___x_87_);
lean_ctor_set(v___x_88_, 1, v_a_66_);
return v___x_88_;
}
default: 
{
lean_object* v_quotContext_89_; lean_object* v_currMacroScope_90_; lean_object* v_ref_91_; uint8_t v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v_quotContext_89_ = lean_ctor_get(v_a_65_, 1);
v_currMacroScope_90_ = lean_ctor_get(v_a_65_, 2);
v_ref_91_ = lean_ctor_get(v_a_65_, 5);
v___x_92_ = 0;
v___x_93_ = l_Lean_SourceInfo_fromRef(v_ref_91_, v___x_92_);
v___x_94_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__20, &l___private_Std_Time_Notation_0__Std_Time_convertText___closed__20_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertText___closed__20);
v___x_95_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertText___closed__22));
lean_inc(v_currMacroScope_90_);
lean_inc(v_quotContext_89_);
v___x_96_ = l_Lean_addMacroScope(v_quotContext_89_, v___x_95_, v_currMacroScope_90_);
v___x_97_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertText___closed__26));
v___x_98_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_98_, 0, v___x_93_);
lean_ctor_set(v___x_98_, 1, v___x_94_);
lean_ctor_set(v___x_98_, 2, v___x_96_);
lean_ctor_set(v___x_98_, 3, v___x_97_);
v___x_99_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_99_, 0, v___x_98_);
lean_ctor_set(v___x_99_, 1, v_a_66_);
return v___x_99_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertText___boxed(lean_object* v_x_100_, lean_object* v_a_101_, lean_object* v_a_102_){
_start:
{
uint8_t v_x_4032__boxed_103_; lean_object* v_res_104_; 
v_x_4032__boxed_103_ = lean_unbox(v_x_100_);
v_res_104_ = l___private_Std_Time_Notation_0__Std_Time_convertText(v_x_4032__boxed_103_, v_a_101_, v_a_102_);
lean_dec_ref(v_a_101_);
return v_res_104_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__6(void){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_115_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__5));
v___x_116_ = l_String_toRawSubstring_x27(v___x_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertNumber(lean_object* v_x_138_, lean_object* v_a_139_, lean_object* v_a_140_){
_start:
{
lean_object* v_quotContext_141_; lean_object* v_currMacroScope_142_; lean_object* v_ref_143_; uint8_t v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v_quotContext_141_ = lean_ctor_get(v_a_139_, 1);
v_currMacroScope_142_ = lean_ctor_get(v_a_139_, 2);
v_ref_143_ = lean_ctor_get(v_a_139_, 5);
v___x_144_ = 0;
v___x_145_ = l_Lean_SourceInfo_fromRef(v_ref_143_, v___x_144_);
v___x_146_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_147_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__6, &l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__6_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__6);
v___x_148_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__9));
lean_inc(v_currMacroScope_142_);
lean_inc(v_quotContext_141_);
v___x_149_ = l_Lean_addMacroScope(v_quotContext_141_, v___x_148_, v_currMacroScope_142_);
v___x_150_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__13));
lean_inc_n(v___x_145_, 2);
v___x_151_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_151_, 0, v___x_145_);
lean_ctor_set(v___x_151_, 1, v___x_147_);
lean_ctor_set(v___x_151_, 2, v___x_149_);
lean_ctor_set(v___x_151_, 3, v___x_150_);
v___x_152_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_153_ = l_Nat_reprFast(v_x_138_);
v___x_154_ = lean_box(2);
v___x_155_ = l_Lean_Syntax_mkNumLit(v___x_153_, v___x_154_);
v___x_156_ = l_Lean_Syntax_node1(v___x_145_, v___x_152_, v___x_155_);
v___x_157_ = l_Lean_Syntax_node2(v___x_145_, v___x_146_, v___x_151_, v___x_156_);
v___x_158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_158_, 0, v___x_157_);
lean_ctor_set(v___x_158_, 1, v_a_140_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertNumber___boxed(lean_object* v_x_159_, lean_object* v_a_160_, lean_object* v_a_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l___private_Std_Time_Notation_0__Std_Time_convertNumber(v_x_159_, v_a_160_, v_a_161_);
lean_dec_ref(v_a_160_);
return v_res_162_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__1(void){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_164_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__0));
v___x_165_ = l_String_toRawSubstring_x27(v___x_164_);
return v___x_165_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__10(void){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_185_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__9));
v___x_186_ = l_String_toRawSubstring_x27(v___x_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertFraction(lean_object* v_x_204_, lean_object* v_a_205_, lean_object* v_a_206_){
_start:
{
if (lean_obj_tag(v_x_204_) == 0)
{
lean_object* v_quotContext_207_; lean_object* v_currMacroScope_208_; lean_object* v_ref_209_; uint8_t v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v_quotContext_207_ = lean_ctor_get(v_a_205_, 1);
v_currMacroScope_208_ = lean_ctor_get(v_a_205_, 2);
v_ref_209_ = lean_ctor_get(v_a_205_, 5);
v___x_210_ = 0;
v___x_211_ = l_Lean_SourceInfo_fromRef(v_ref_209_, v___x_210_);
v___x_212_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__1, &l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__1_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__1);
v___x_213_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__4));
lean_inc(v_currMacroScope_208_);
lean_inc(v_quotContext_207_);
v___x_214_ = l_Lean_addMacroScope(v_quotContext_207_, v___x_213_, v_currMacroScope_208_);
v___x_215_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__8));
v___x_216_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_216_, 0, v___x_211_);
lean_ctor_set(v___x_216_, 1, v___x_212_);
lean_ctor_set(v___x_216_, 2, v___x_214_);
lean_ctor_set(v___x_216_, 3, v___x_215_);
v___x_217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_217_, 0, v___x_216_);
lean_ctor_set(v___x_217_, 1, v_a_206_);
return v___x_217_;
}
else
{
lean_object* v_digits_218_; lean_object* v_quotContext_219_; lean_object* v_currMacroScope_220_; lean_object* v_ref_221_; uint8_t v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v_digits_218_ = lean_ctor_get(v_x_204_, 0);
lean_inc(v_digits_218_);
lean_dec_ref_known(v_x_204_, 1);
v_quotContext_219_ = lean_ctor_get(v_a_205_, 1);
v_currMacroScope_220_ = lean_ctor_get(v_a_205_, 2);
v_ref_221_ = lean_ctor_get(v_a_205_, 5);
v___x_222_ = 0;
v___x_223_ = l_Lean_SourceInfo_fromRef(v_ref_221_, v___x_222_);
v___x_224_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_225_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__10, &l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__10_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__10);
v___x_226_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__12));
lean_inc(v_currMacroScope_220_);
lean_inc(v_quotContext_219_);
v___x_227_ = l_Lean_addMacroScope(v_quotContext_219_, v___x_226_, v_currMacroScope_220_);
v___x_228_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__16));
lean_inc_n(v___x_223_, 2);
v___x_229_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_229_, 0, v___x_223_);
lean_ctor_set(v___x_229_, 1, v___x_225_);
lean_ctor_set(v___x_229_, 2, v___x_227_);
lean_ctor_set(v___x_229_, 3, v___x_228_);
v___x_230_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_231_ = l_Nat_reprFast(v_digits_218_);
v___x_232_ = lean_box(2);
v___x_233_ = l_Lean_Syntax_mkNumLit(v___x_231_, v___x_232_);
v___x_234_ = l_Lean_Syntax_node1(v___x_223_, v___x_230_, v___x_233_);
v___x_235_ = l_Lean_Syntax_node2(v___x_223_, v___x_224_, v___x_229_, v___x_234_);
v___x_236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_236_, 0, v___x_235_);
lean_ctor_set(v___x_236_, 1, v_a_206_);
return v___x_236_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertFraction___boxed(lean_object* v_x_237_, lean_object* v_a_238_, lean_object* v_a_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l___private_Std_Time_Notation_0__Std_Time_convertFraction(v_x_237_, v_a_238_, v_a_239_);
lean_dec_ref(v_a_238_);
return v_res_240_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__1(void){
_start:
{
lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_242_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__0));
v___x_243_ = l_String_toRawSubstring_x27(v___x_242_);
return v___x_243_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__10(void){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_263_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__9));
v___x_264_ = l_String_toRawSubstring_x27(v___x_263_);
return v___x_264_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__18(void){
_start:
{
lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_283_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__17));
v___x_284_ = l_String_toRawSubstring_x27(v___x_283_);
return v___x_284_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__26(void){
_start:
{
lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_303_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__25));
v___x_304_ = l_String_toRawSubstring_x27(v___x_303_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertYear(lean_object* v_x_322_, lean_object* v_a_323_, lean_object* v_a_324_){
_start:
{
switch(lean_obj_tag(v_x_322_))
{
case 0:
{
lean_object* v_quotContext_325_; lean_object* v_currMacroScope_326_; lean_object* v_ref_327_; uint8_t v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v_quotContext_325_ = lean_ctor_get(v_a_323_, 1);
v_currMacroScope_326_ = lean_ctor_get(v_a_323_, 2);
v_ref_327_ = lean_ctor_get(v_a_323_, 5);
v___x_328_ = 0;
v___x_329_ = l_Lean_SourceInfo_fromRef(v_ref_327_, v___x_328_);
v___x_330_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__1, &l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__1_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__1);
v___x_331_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__4));
lean_inc(v_currMacroScope_326_);
lean_inc(v_quotContext_325_);
v___x_332_ = l_Lean_addMacroScope(v_quotContext_325_, v___x_331_, v_currMacroScope_326_);
v___x_333_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__8));
v___x_334_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_334_, 0, v___x_329_);
lean_ctor_set(v___x_334_, 1, v___x_330_);
lean_ctor_set(v___x_334_, 2, v___x_332_);
lean_ctor_set(v___x_334_, 3, v___x_333_);
v___x_335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
lean_ctor_set(v___x_335_, 1, v_a_324_);
return v___x_335_;
}
case 1:
{
lean_object* v_quotContext_336_; lean_object* v_currMacroScope_337_; lean_object* v_ref_338_; uint8_t v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v_quotContext_336_ = lean_ctor_get(v_a_323_, 1);
v_currMacroScope_337_ = lean_ctor_get(v_a_323_, 2);
v_ref_338_ = lean_ctor_get(v_a_323_, 5);
v___x_339_ = 0;
v___x_340_ = l_Lean_SourceInfo_fromRef(v_ref_338_, v___x_339_);
v___x_341_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__10, &l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__10_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__10);
v___x_342_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__12));
lean_inc(v_currMacroScope_337_);
lean_inc(v_quotContext_336_);
v___x_343_ = l_Lean_addMacroScope(v_quotContext_336_, v___x_342_, v_currMacroScope_337_);
v___x_344_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__16));
v___x_345_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_345_, 0, v___x_340_);
lean_ctor_set(v___x_345_, 1, v___x_341_);
lean_ctor_set(v___x_345_, 2, v___x_343_);
lean_ctor_set(v___x_345_, 3, v___x_344_);
v___x_346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_346_, 0, v___x_345_);
lean_ctor_set(v___x_346_, 1, v_a_324_);
return v___x_346_;
}
case 2:
{
lean_object* v_quotContext_347_; lean_object* v_currMacroScope_348_; lean_object* v_ref_349_; uint8_t v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
v_quotContext_347_ = lean_ctor_get(v_a_323_, 1);
v_currMacroScope_348_ = lean_ctor_get(v_a_323_, 2);
v_ref_349_ = lean_ctor_get(v_a_323_, 5);
v___x_350_ = 0;
v___x_351_ = l_Lean_SourceInfo_fromRef(v_ref_349_, v___x_350_);
v___x_352_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__18, &l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__18_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__18);
v___x_353_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__20));
lean_inc(v_currMacroScope_348_);
lean_inc(v_quotContext_347_);
v___x_354_ = l_Lean_addMacroScope(v_quotContext_347_, v___x_353_, v_currMacroScope_348_);
v___x_355_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__24));
v___x_356_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_356_, 0, v___x_351_);
lean_ctor_set(v___x_356_, 1, v___x_352_);
lean_ctor_set(v___x_356_, 2, v___x_354_);
lean_ctor_set(v___x_356_, 3, v___x_355_);
v___x_357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_357_, 0, v___x_356_);
lean_ctor_set(v___x_357_, 1, v_a_324_);
return v___x_357_;
}
default: 
{
lean_object* v_num_358_; lean_object* v_quotContext_359_; lean_object* v_currMacroScope_360_; lean_object* v_ref_361_; uint8_t v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v_num_358_ = lean_ctor_get(v_x_322_, 0);
lean_inc(v_num_358_);
lean_dec_ref_known(v_x_322_, 1);
v_quotContext_359_ = lean_ctor_get(v_a_323_, 1);
v_currMacroScope_360_ = lean_ctor_get(v_a_323_, 2);
v_ref_361_ = lean_ctor_get(v_a_323_, 5);
v___x_362_ = 0;
v___x_363_ = l_Lean_SourceInfo_fromRef(v_ref_361_, v___x_362_);
v___x_364_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_365_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__26, &l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__26_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__26);
v___x_366_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__28));
lean_inc(v_currMacroScope_360_);
lean_inc(v_quotContext_359_);
v___x_367_ = l_Lean_addMacroScope(v_quotContext_359_, v___x_366_, v_currMacroScope_360_);
v___x_368_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__32));
lean_inc_n(v___x_363_, 2);
v___x_369_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_369_, 0, v___x_363_);
lean_ctor_set(v___x_369_, 1, v___x_365_);
lean_ctor_set(v___x_369_, 2, v___x_367_);
lean_ctor_set(v___x_369_, 3, v___x_368_);
v___x_370_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_371_ = l_Nat_reprFast(v_num_358_);
v___x_372_ = lean_box(2);
v___x_373_ = l_Lean_Syntax_mkNumLit(v___x_371_, v___x_372_);
v___x_374_ = l_Lean_Syntax_node1(v___x_363_, v___x_370_, v___x_373_);
v___x_375_ = l_Lean_Syntax_node2(v___x_363_, v___x_364_, v___x_369_, v___x_374_);
v___x_376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_376_, 0, v___x_375_);
lean_ctor_set(v___x_376_, 1, v_a_324_);
return v___x_376_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertYear___boxed(lean_object* v_x_377_, lean_object* v_a_378_, lean_object* v_a_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l___private_Std_Time_Notation_0__Std_Time_convertYear(v_x_377_, v_a_378_, v_a_379_);
lean_dec_ref(v_a_378_);
return v_res_380_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__1(void){
_start:
{
lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_382_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__0));
v___x_383_ = l_String_toRawSubstring_x27(v___x_382_);
return v___x_383_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__9(void){
_start:
{
lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_402_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__8));
v___x_403_ = l_String_toRawSubstring_x27(v___x_402_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZoneName(uint8_t v_x_420_, lean_object* v_a_421_, lean_object* v_a_422_){
_start:
{
if (v_x_420_ == 0)
{
lean_object* v_quotContext_423_; lean_object* v_currMacroScope_424_; lean_object* v_ref_425_; uint8_t v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v_quotContext_423_ = lean_ctor_get(v_a_421_, 1);
v_currMacroScope_424_ = lean_ctor_get(v_a_421_, 2);
v_ref_425_ = lean_ctor_get(v_a_421_, 5);
v___x_426_ = 0;
v___x_427_ = l_Lean_SourceInfo_fromRef(v_ref_425_, v___x_426_);
v___x_428_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__1, &l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__1_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__1);
v___x_429_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__3));
lean_inc(v_currMacroScope_424_);
lean_inc(v_quotContext_423_);
v___x_430_ = l_Lean_addMacroScope(v_quotContext_423_, v___x_429_, v_currMacroScope_424_);
v___x_431_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__7));
v___x_432_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_432_, 0, v___x_427_);
lean_ctor_set(v___x_432_, 1, v___x_428_);
lean_ctor_set(v___x_432_, 2, v___x_430_);
lean_ctor_set(v___x_432_, 3, v___x_431_);
v___x_433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_433_, 0, v___x_432_);
lean_ctor_set(v___x_433_, 1, v_a_422_);
return v___x_433_;
}
else
{
lean_object* v_quotContext_434_; lean_object* v_currMacroScope_435_; lean_object* v_ref_436_; uint8_t v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v_quotContext_434_ = lean_ctor_get(v_a_421_, 1);
v_currMacroScope_435_ = lean_ctor_get(v_a_421_, 2);
v_ref_436_ = lean_ctor_get(v_a_421_, 5);
v___x_437_ = 0;
v___x_438_ = l_Lean_SourceInfo_fromRef(v_ref_436_, v___x_437_);
v___x_439_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__9, &l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__9_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__9);
v___x_440_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__10));
lean_inc(v_currMacroScope_435_);
lean_inc(v_quotContext_434_);
v___x_441_ = l_Lean_addMacroScope(v_quotContext_434_, v___x_440_, v_currMacroScope_435_);
v___x_442_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__14));
v___x_443_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_443_, 0, v___x_438_);
lean_ctor_set(v___x_443_, 1, v___x_439_);
lean_ctor_set(v___x_443_, 2, v___x_441_);
lean_ctor_set(v___x_443_, 3, v___x_442_);
v___x_444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_444_, 0, v___x_443_);
lean_ctor_set(v___x_444_, 1, v_a_422_);
return v___x_444_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZoneName___boxed(lean_object* v_x_445_, lean_object* v_a_446_, lean_object* v_a_447_){
_start:
{
uint8_t v_x_2689__boxed_448_; lean_object* v_res_449_; 
v_x_2689__boxed_448_ = lean_unbox(v_x_445_);
v_res_449_ = l___private_Std_Time_Notation_0__Std_Time_convertZoneName(v_x_2689__boxed_448_, v_a_446_, v_a_447_);
lean_dec_ref(v_a_446_);
return v_res_449_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__1(void){
_start:
{
lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_451_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__0));
v___x_452_ = l_String_toRawSubstring_x27(v___x_451_);
return v___x_452_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__10(void){
_start:
{
lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_472_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__9));
v___x_473_ = l_String_toRawSubstring_x27(v___x_472_);
return v___x_473_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__18(void){
_start:
{
lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_492_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__17));
v___x_493_ = l_String_toRawSubstring_x27(v___x_492_);
return v___x_493_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__26(void){
_start:
{
lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_512_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__25));
v___x_513_ = l_String_toRawSubstring_x27(v___x_512_);
return v___x_513_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__34(void){
_start:
{
lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_532_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__33));
v___x_533_ = l_String_toRawSubstring_x27(v___x_532_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetX(uint8_t v_x_551_, lean_object* v_a_552_, lean_object* v_a_553_){
_start:
{
switch(v_x_551_)
{
case 0:
{
lean_object* v_quotContext_554_; lean_object* v_currMacroScope_555_; lean_object* v_ref_556_; uint8_t v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
v_quotContext_554_ = lean_ctor_get(v_a_552_, 1);
v_currMacroScope_555_ = lean_ctor_get(v_a_552_, 2);
v_ref_556_ = lean_ctor_get(v_a_552_, 5);
v___x_557_ = 0;
v___x_558_ = l_Lean_SourceInfo_fromRef(v_ref_556_, v___x_557_);
v___x_559_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__1, &l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__1_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__1);
v___x_560_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__4));
lean_inc(v_currMacroScope_555_);
lean_inc(v_quotContext_554_);
v___x_561_ = l_Lean_addMacroScope(v_quotContext_554_, v___x_560_, v_currMacroScope_555_);
v___x_562_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__8));
v___x_563_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_563_, 0, v___x_558_);
lean_ctor_set(v___x_563_, 1, v___x_559_);
lean_ctor_set(v___x_563_, 2, v___x_561_);
lean_ctor_set(v___x_563_, 3, v___x_562_);
v___x_564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_564_, 0, v___x_563_);
lean_ctor_set(v___x_564_, 1, v_a_553_);
return v___x_564_;
}
case 1:
{
lean_object* v_quotContext_565_; lean_object* v_currMacroScope_566_; lean_object* v_ref_567_; uint8_t v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v_quotContext_565_ = lean_ctor_get(v_a_552_, 1);
v_currMacroScope_566_ = lean_ctor_get(v_a_552_, 2);
v_ref_567_ = lean_ctor_get(v_a_552_, 5);
v___x_568_ = 0;
v___x_569_ = l_Lean_SourceInfo_fromRef(v_ref_567_, v___x_568_);
v___x_570_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__10, &l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__10_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__10);
v___x_571_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__12));
lean_inc(v_currMacroScope_566_);
lean_inc(v_quotContext_565_);
v___x_572_ = l_Lean_addMacroScope(v_quotContext_565_, v___x_571_, v_currMacroScope_566_);
v___x_573_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__16));
v___x_574_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_574_, 0, v___x_569_);
lean_ctor_set(v___x_574_, 1, v___x_570_);
lean_ctor_set(v___x_574_, 2, v___x_572_);
lean_ctor_set(v___x_574_, 3, v___x_573_);
v___x_575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_575_, 0, v___x_574_);
lean_ctor_set(v___x_575_, 1, v_a_553_);
return v___x_575_;
}
case 2:
{
lean_object* v_quotContext_576_; lean_object* v_currMacroScope_577_; lean_object* v_ref_578_; uint8_t v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
v_quotContext_576_ = lean_ctor_get(v_a_552_, 1);
v_currMacroScope_577_ = lean_ctor_get(v_a_552_, 2);
v_ref_578_ = lean_ctor_get(v_a_552_, 5);
v___x_579_ = 0;
v___x_580_ = l_Lean_SourceInfo_fromRef(v_ref_578_, v___x_579_);
v___x_581_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__18, &l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__18_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__18);
v___x_582_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__20));
lean_inc(v_currMacroScope_577_);
lean_inc(v_quotContext_576_);
v___x_583_ = l_Lean_addMacroScope(v_quotContext_576_, v___x_582_, v_currMacroScope_577_);
v___x_584_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__24));
v___x_585_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_585_, 0, v___x_580_);
lean_ctor_set(v___x_585_, 1, v___x_581_);
lean_ctor_set(v___x_585_, 2, v___x_583_);
lean_ctor_set(v___x_585_, 3, v___x_584_);
v___x_586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_586_, 0, v___x_585_);
lean_ctor_set(v___x_586_, 1, v_a_553_);
return v___x_586_;
}
case 3:
{
lean_object* v_quotContext_587_; lean_object* v_currMacroScope_588_; lean_object* v_ref_589_; uint8_t v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
v_quotContext_587_ = lean_ctor_get(v_a_552_, 1);
v_currMacroScope_588_ = lean_ctor_get(v_a_552_, 2);
v_ref_589_ = lean_ctor_get(v_a_552_, 5);
v___x_590_ = 0;
v___x_591_ = l_Lean_SourceInfo_fromRef(v_ref_589_, v___x_590_);
v___x_592_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__26, &l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__26_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__26);
v___x_593_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__28));
lean_inc(v_currMacroScope_588_);
lean_inc(v_quotContext_587_);
v___x_594_ = l_Lean_addMacroScope(v_quotContext_587_, v___x_593_, v_currMacroScope_588_);
v___x_595_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__32));
v___x_596_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_596_, 0, v___x_591_);
lean_ctor_set(v___x_596_, 1, v___x_592_);
lean_ctor_set(v___x_596_, 2, v___x_594_);
lean_ctor_set(v___x_596_, 3, v___x_595_);
v___x_597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_597_, 0, v___x_596_);
lean_ctor_set(v___x_597_, 1, v_a_553_);
return v___x_597_;
}
default: 
{
lean_object* v_quotContext_598_; lean_object* v_currMacroScope_599_; lean_object* v_ref_600_; uint8_t v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
v_quotContext_598_ = lean_ctor_get(v_a_552_, 1);
v_currMacroScope_599_ = lean_ctor_get(v_a_552_, 2);
v_ref_600_ = lean_ctor_get(v_a_552_, 5);
v___x_601_ = 0;
v___x_602_ = l_Lean_SourceInfo_fromRef(v_ref_600_, v___x_601_);
v___x_603_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__34, &l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__34_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__34);
v___x_604_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__36));
lean_inc(v_currMacroScope_599_);
lean_inc(v_quotContext_598_);
v___x_605_ = l_Lean_addMacroScope(v_quotContext_598_, v___x_604_, v_currMacroScope_599_);
v___x_606_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__40));
v___x_607_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_607_, 0, v___x_602_);
lean_ctor_set(v___x_607_, 1, v___x_603_);
lean_ctor_set(v___x_607_, 2, v___x_605_);
lean_ctor_set(v___x_607_, 3, v___x_606_);
v___x_608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_608_, 0, v___x_607_);
lean_ctor_set(v___x_608_, 1, v_a_553_);
return v___x_608_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___boxed(lean_object* v_x_609_, lean_object* v_a_610_, lean_object* v_a_611_){
_start:
{
uint8_t v_x_6708__boxed_612_; lean_object* v_res_613_; 
v_x_6708__boxed_612_ = lean_unbox(v_x_609_);
v_res_613_ = l___private_Std_Time_Notation_0__Std_Time_convertOffsetX(v_x_6708__boxed_612_, v_a_610_, v_a_611_);
lean_dec_ref(v_a_610_);
return v_res_613_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__1(void){
_start:
{
lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_615_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__0));
v___x_616_ = l_String_toRawSubstring_x27(v___x_615_);
return v___x_616_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__9(void){
_start:
{
lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_635_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__8));
v___x_636_ = l_String_toRawSubstring_x27(v___x_635_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetO(uint8_t v_x_653_, lean_object* v_a_654_, lean_object* v_a_655_){
_start:
{
if (v_x_653_ == 0)
{
lean_object* v_quotContext_656_; lean_object* v_currMacroScope_657_; lean_object* v_ref_658_; uint8_t v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; 
v_quotContext_656_ = lean_ctor_get(v_a_654_, 1);
v_currMacroScope_657_ = lean_ctor_get(v_a_654_, 2);
v_ref_658_ = lean_ctor_get(v_a_654_, 5);
v___x_659_ = 0;
v___x_660_ = l_Lean_SourceInfo_fromRef(v_ref_658_, v___x_659_);
v___x_661_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__1, &l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__1_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__1);
v___x_662_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__3));
lean_inc(v_currMacroScope_657_);
lean_inc(v_quotContext_656_);
v___x_663_ = l_Lean_addMacroScope(v_quotContext_656_, v___x_662_, v_currMacroScope_657_);
v___x_664_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__7));
v___x_665_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_665_, 0, v___x_660_);
lean_ctor_set(v___x_665_, 1, v___x_661_);
lean_ctor_set(v___x_665_, 2, v___x_663_);
lean_ctor_set(v___x_665_, 3, v___x_664_);
v___x_666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_666_, 0, v___x_665_);
lean_ctor_set(v___x_666_, 1, v_a_655_);
return v___x_666_;
}
else
{
lean_object* v_quotContext_667_; lean_object* v_currMacroScope_668_; lean_object* v_ref_669_; uint8_t v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v_quotContext_667_ = lean_ctor_get(v_a_654_, 1);
v_currMacroScope_668_ = lean_ctor_get(v_a_654_, 2);
v_ref_669_ = lean_ctor_get(v_a_654_, 5);
v___x_670_ = 0;
v___x_671_ = l_Lean_SourceInfo_fromRef(v_ref_669_, v___x_670_);
v___x_672_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__9, &l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__9_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__9);
v___x_673_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__10));
lean_inc(v_currMacroScope_668_);
lean_inc(v_quotContext_667_);
v___x_674_ = l_Lean_addMacroScope(v_quotContext_667_, v___x_673_, v_currMacroScope_668_);
v___x_675_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__14));
v___x_676_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_676_, 0, v___x_671_);
lean_ctor_set(v___x_676_, 1, v___x_672_);
lean_ctor_set(v___x_676_, 2, v___x_674_);
lean_ctor_set(v___x_676_, 3, v___x_675_);
v___x_677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_677_, 0, v___x_676_);
lean_ctor_set(v___x_677_, 1, v_a_655_);
return v___x_677_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___boxed(lean_object* v_x_678_, lean_object* v_a_679_, lean_object* v_a_680_){
_start:
{
uint8_t v_x_2689__boxed_681_; lean_object* v_res_682_; 
v_x_2689__boxed_681_ = lean_unbox(v_x_678_);
v_res_682_ = l___private_Std_Time_Notation_0__Std_Time_convertOffsetO(v_x_2689__boxed_681_, v_a_679_, v_a_680_);
lean_dec_ref(v_a_679_);
return v_res_682_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__1(void){
_start:
{
lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_684_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__0));
v___x_685_ = l_String_toRawSubstring_x27(v___x_684_);
return v___x_685_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__9(void){
_start:
{
lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_704_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__8));
v___x_705_ = l_String_toRawSubstring_x27(v___x_704_);
return v___x_705_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__16(void){
_start:
{
lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_723_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__15));
v___x_724_ = l_String_toRawSubstring_x27(v___x_723_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ(uint8_t v_x_741_, lean_object* v_a_742_, lean_object* v_a_743_){
_start:
{
switch(v_x_741_)
{
case 0:
{
lean_object* v_quotContext_744_; lean_object* v_currMacroScope_745_; lean_object* v_ref_746_; uint8_t v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; 
v_quotContext_744_ = lean_ctor_get(v_a_742_, 1);
v_currMacroScope_745_ = lean_ctor_get(v_a_742_, 2);
v_ref_746_ = lean_ctor_get(v_a_742_, 5);
v___x_747_ = 0;
v___x_748_ = l_Lean_SourceInfo_fromRef(v_ref_746_, v___x_747_);
v___x_749_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__1, &l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__1_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__1);
v___x_750_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__3));
lean_inc(v_currMacroScope_745_);
lean_inc(v_quotContext_744_);
v___x_751_ = l_Lean_addMacroScope(v_quotContext_744_, v___x_750_, v_currMacroScope_745_);
v___x_752_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__7));
v___x_753_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_753_, 0, v___x_748_);
lean_ctor_set(v___x_753_, 1, v___x_749_);
lean_ctor_set(v___x_753_, 2, v___x_751_);
lean_ctor_set(v___x_753_, 3, v___x_752_);
v___x_754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_754_, 0, v___x_753_);
lean_ctor_set(v___x_754_, 1, v_a_743_);
return v___x_754_;
}
case 1:
{
lean_object* v_quotContext_755_; lean_object* v_currMacroScope_756_; lean_object* v_ref_757_; uint8_t v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
v_quotContext_755_ = lean_ctor_get(v_a_742_, 1);
v_currMacroScope_756_ = lean_ctor_get(v_a_742_, 2);
v_ref_757_ = lean_ctor_get(v_a_742_, 5);
v___x_758_ = 0;
v___x_759_ = l_Lean_SourceInfo_fromRef(v_ref_757_, v___x_758_);
v___x_760_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__9, &l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__9_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__9);
v___x_761_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__10));
lean_inc(v_currMacroScope_756_);
lean_inc(v_quotContext_755_);
v___x_762_ = l_Lean_addMacroScope(v_quotContext_755_, v___x_761_, v_currMacroScope_756_);
v___x_763_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__14));
v___x_764_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_764_, 0, v___x_759_);
lean_ctor_set(v___x_764_, 1, v___x_760_);
lean_ctor_set(v___x_764_, 2, v___x_762_);
lean_ctor_set(v___x_764_, 3, v___x_763_);
v___x_765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_765_, 0, v___x_764_);
lean_ctor_set(v___x_765_, 1, v_a_743_);
return v___x_765_;
}
default: 
{
lean_object* v_quotContext_766_; lean_object* v_currMacroScope_767_; lean_object* v_ref_768_; uint8_t v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
v_quotContext_766_ = lean_ctor_get(v_a_742_, 1);
v_currMacroScope_767_ = lean_ctor_get(v_a_742_, 2);
v_ref_768_ = lean_ctor_get(v_a_742_, 5);
v___x_769_ = 0;
v___x_770_ = l_Lean_SourceInfo_fromRef(v_ref_768_, v___x_769_);
v___x_771_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__16, &l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__16_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__16);
v___x_772_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__17));
lean_inc(v_currMacroScope_767_);
lean_inc(v_quotContext_766_);
v___x_773_ = l_Lean_addMacroScope(v_quotContext_766_, v___x_772_, v_currMacroScope_767_);
v___x_774_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__21));
v___x_775_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_775_, 0, v___x_770_);
lean_ctor_set(v___x_775_, 1, v___x_771_);
lean_ctor_set(v___x_775_, 2, v___x_773_);
lean_ctor_set(v___x_775_, 3, v___x_774_);
v___x_776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_776_, 0, v___x_775_);
lean_ctor_set(v___x_776_, 1, v_a_743_);
return v___x_776_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___boxed(lean_object* v_x_777_, lean_object* v_a_778_, lean_object* v_a_779_){
_start:
{
uint8_t v_x_4027__boxed_780_; lean_object* v_res_781_; 
v_x_4027__boxed_780_ = lean_unbox(v_x_777_);
v_res_781_ = l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ(v_x_4027__boxed_780_, v_a_778_, v_a_779_);
lean_dec_ref(v_a_778_);
return v_res_781_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__1(void){
_start:
{
lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_783_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__0));
v___x_784_ = l_String_toRawSubstring_x27(v___x_783_);
return v___x_784_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__10(void){
_start:
{
lean_object* v___x_804_; lean_object* v___x_805_; 
v___x_804_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__9));
v___x_805_ = l_String_toRawSubstring_x27(v___x_804_);
return v___x_805_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__18(void){
_start:
{
lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_824_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__17));
v___x_825_ = l_String_toRawSubstring_x27(v___x_824_);
return v___x_825_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__26(void){
_start:
{
lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_844_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__25));
v___x_845_ = l_String_toRawSubstring_x27(v___x_844_);
return v___x_845_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__34(void){
_start:
{
lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_864_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__33));
v___x_865_ = l_String_toRawSubstring_x27(v___x_864_);
return v___x_865_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__42(void){
_start:
{
lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_884_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__41));
v___x_885_ = l_String_toRawSubstring_x27(v___x_884_);
return v___x_885_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__57(void){
_start:
{
lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_920_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__56));
v___x_921_ = l_String_toRawSubstring_x27(v___x_920_);
return v___x_921_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__78(void){
_start:
{
lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_970_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__77));
v___x_971_ = l_String_toRawSubstring_x27(v___x_970_);
return v___x_971_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__82(void){
_start:
{
lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_976_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__81));
v___x_977_ = l_String_toRawSubstring_x27(v___x_976_);
return v___x_977_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__85(void){
_start:
{
lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_981_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__84));
v___x_982_ = l_String_toRawSubstring_x27(v___x_981_);
return v___x_982_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__93(void){
_start:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_1001_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__92));
v___x_1002_ = l_String_toRawSubstring_x27(v___x_1001_);
return v___x_1002_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__101(void){
_start:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1021_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__100));
v___x_1022_ = l_String_toRawSubstring_x27(v___x_1021_);
return v___x_1022_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__109(void){
_start:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1041_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__108));
v___x_1042_ = l_String_toRawSubstring_x27(v___x_1041_);
return v___x_1042_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__117(void){
_start:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; 
v___x_1061_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__116));
v___x_1062_ = l_String_toRawSubstring_x27(v___x_1061_);
return v___x_1062_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__125(void){
_start:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1081_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__124));
v___x_1082_ = l_String_toRawSubstring_x27(v___x_1081_);
return v___x_1082_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__133(void){
_start:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1101_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__132));
v___x_1102_ = l_String_toRawSubstring_x27(v___x_1101_);
return v___x_1102_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__141(void){
_start:
{
lean_object* v___x_1121_; lean_object* v___x_1122_; 
v___x_1121_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__140));
v___x_1122_ = l_String_toRawSubstring_x27(v___x_1121_);
return v___x_1122_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__149(void){
_start:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1141_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__148));
v___x_1142_ = l_String_toRawSubstring_x27(v___x_1141_);
return v___x_1142_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__157(void){
_start:
{
lean_object* v___x_1161_; lean_object* v___x_1162_; 
v___x_1161_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__156));
v___x_1162_ = l_String_toRawSubstring_x27(v___x_1161_);
return v___x_1162_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__165(void){
_start:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; 
v___x_1181_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__164));
v___x_1182_ = l_String_toRawSubstring_x27(v___x_1181_);
return v___x_1182_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__173(void){
_start:
{
lean_object* v___x_1201_; lean_object* v___x_1202_; 
v___x_1201_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__172));
v___x_1202_ = l_String_toRawSubstring_x27(v___x_1201_);
return v___x_1202_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__181(void){
_start:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1221_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__180));
v___x_1222_ = l_String_toRawSubstring_x27(v___x_1221_);
return v___x_1222_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__189(void){
_start:
{
lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1241_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__188));
v___x_1242_ = l_String_toRawSubstring_x27(v___x_1241_);
return v___x_1242_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__197(void){
_start:
{
lean_object* v___x_1261_; lean_object* v___x_1262_; 
v___x_1261_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__196));
v___x_1262_ = l_String_toRawSubstring_x27(v___x_1261_);
return v___x_1262_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__205(void){
_start:
{
lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1281_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__204));
v___x_1282_ = l_String_toRawSubstring_x27(v___x_1281_);
return v___x_1282_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__213(void){
_start:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1301_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__212));
v___x_1302_ = l_String_toRawSubstring_x27(v___x_1301_);
return v___x_1302_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__221(void){
_start:
{
lean_object* v___x_1321_; lean_object* v___x_1322_; 
v___x_1321_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__220));
v___x_1322_ = l_String_toRawSubstring_x27(v___x_1321_);
return v___x_1322_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__229(void){
_start:
{
lean_object* v___x_1341_; lean_object* v___x_1342_; 
v___x_1341_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__228));
v___x_1342_ = l_String_toRawSubstring_x27(v___x_1341_);
return v___x_1342_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__237(void){
_start:
{
lean_object* v___x_1361_; lean_object* v___x_1362_; 
v___x_1361_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__236));
v___x_1362_ = l_String_toRawSubstring_x27(v___x_1361_);
return v___x_1362_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__245(void){
_start:
{
lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1381_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__244));
v___x_1382_ = l_String_toRawSubstring_x27(v___x_1381_);
return v___x_1382_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__253(void){
_start:
{
lean_object* v___x_1401_; lean_object* v___x_1402_; 
v___x_1401_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__252));
v___x_1402_ = l_String_toRawSubstring_x27(v___x_1401_);
return v___x_1402_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__261(void){
_start:
{
lean_object* v___x_1421_; lean_object* v___x_1422_; 
v___x_1421_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__260));
v___x_1422_ = l_String_toRawSubstring_x27(v___x_1421_);
return v___x_1422_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__269(void){
_start:
{
lean_object* v___x_1441_; lean_object* v___x_1442_; 
v___x_1441_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__268));
v___x_1442_ = l_String_toRawSubstring_x27(v___x_1441_);
return v___x_1442_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier(lean_object* v_x_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_){
_start:
{
switch(lean_obj_tag(v_x_1460_))
{
case 0:
{
uint8_t v_presentation_1463_; lean_object* v___x_1464_; lean_object* v_a_1465_; lean_object* v_a_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1487_; 
v_presentation_1463_ = lean_ctor_get_uint8(v_x_1460_, 0);
lean_dec_ref_known(v_x_1460_, 0);
v___x_1464_ = l___private_Std_Time_Notation_0__Std_Time_convertText(v_presentation_1463_, v_a_1461_, v_a_1462_);
v_a_1465_ = lean_ctor_get(v___x_1464_, 0);
v_a_1466_ = lean_ctor_get(v___x_1464_, 1);
v_isSharedCheck_1487_ = !lean_is_exclusive(v___x_1464_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1468_ = v___x_1464_;
v_isShared_1469_ = v_isSharedCheck_1487_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_a_1466_);
lean_inc(v_a_1465_);
lean_dec(v___x_1464_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1487_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v_quotContext_1470_; lean_object* v_currMacroScope_1471_; lean_object* v_ref_1472_; uint8_t v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1485_; 
v_quotContext_1470_ = lean_ctor_get(v_a_1461_, 1);
v_currMacroScope_1471_ = lean_ctor_get(v_a_1461_, 2);
v_ref_1472_ = lean_ctor_get(v_a_1461_, 5);
v___x_1473_ = 0;
v___x_1474_ = l_Lean_SourceInfo_fromRef(v_ref_1472_, v___x_1473_);
v___x_1475_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_1476_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__1, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__1_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__1);
v___x_1477_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__4));
lean_inc(v_currMacroScope_1471_);
lean_inc(v_quotContext_1470_);
v___x_1478_ = l_Lean_addMacroScope(v_quotContext_1470_, v___x_1477_, v_currMacroScope_1471_);
v___x_1479_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__8));
lean_inc_n(v___x_1474_, 2);
v___x_1480_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1480_, 0, v___x_1474_);
lean_ctor_set(v___x_1480_, 1, v___x_1476_);
lean_ctor_set(v___x_1480_, 2, v___x_1478_);
lean_ctor_set(v___x_1480_, 3, v___x_1479_);
v___x_1481_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_1482_ = l_Lean_Syntax_node1(v___x_1474_, v___x_1481_, v_a_1465_);
v___x_1483_ = l_Lean_Syntax_node2(v___x_1474_, v___x_1475_, v___x_1480_, v___x_1482_);
if (v_isShared_1469_ == 0)
{
lean_ctor_set(v___x_1468_, 0, v___x_1483_);
v___x_1485_ = v___x_1468_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v___x_1483_);
lean_ctor_set(v_reuseFailAlloc_1486_, 1, v_a_1466_);
v___x_1485_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
return v___x_1485_;
}
}
}
case 1:
{
lean_object* v_presentation_1488_; lean_object* v___x_1489_; lean_object* v_a_1490_; lean_object* v_a_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1512_; 
v_presentation_1488_ = lean_ctor_get(v_x_1460_, 0);
lean_inc(v_presentation_1488_);
lean_dec_ref_known(v_x_1460_, 1);
v___x_1489_ = l___private_Std_Time_Notation_0__Std_Time_convertYear(v_presentation_1488_, v_a_1461_, v_a_1462_);
v_a_1490_ = lean_ctor_get(v___x_1489_, 0);
v_a_1491_ = lean_ctor_get(v___x_1489_, 1);
v_isSharedCheck_1512_ = !lean_is_exclusive(v___x_1489_);
if (v_isSharedCheck_1512_ == 0)
{
v___x_1493_ = v___x_1489_;
v_isShared_1494_ = v_isSharedCheck_1512_;
goto v_resetjp_1492_;
}
else
{
lean_inc(v_a_1491_);
lean_inc(v_a_1490_);
lean_dec(v___x_1489_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1512_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
lean_object* v_quotContext_1495_; lean_object* v_currMacroScope_1496_; lean_object* v_ref_1497_; uint8_t v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1510_; 
v_quotContext_1495_ = lean_ctor_get(v_a_1461_, 1);
v_currMacroScope_1496_ = lean_ctor_get(v_a_1461_, 2);
v_ref_1497_ = lean_ctor_get(v_a_1461_, 5);
v___x_1498_ = 0;
v___x_1499_ = l_Lean_SourceInfo_fromRef(v_ref_1497_, v___x_1498_);
v___x_1500_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_1501_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__10, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__10_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__10);
v___x_1502_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__12));
lean_inc(v_currMacroScope_1496_);
lean_inc(v_quotContext_1495_);
v___x_1503_ = l_Lean_addMacroScope(v_quotContext_1495_, v___x_1502_, v_currMacroScope_1496_);
v___x_1504_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__16));
lean_inc_n(v___x_1499_, 2);
v___x_1505_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1505_, 0, v___x_1499_);
lean_ctor_set(v___x_1505_, 1, v___x_1501_);
lean_ctor_set(v___x_1505_, 2, v___x_1503_);
lean_ctor_set(v___x_1505_, 3, v___x_1504_);
v___x_1506_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_1507_ = l_Lean_Syntax_node1(v___x_1499_, v___x_1506_, v_a_1490_);
v___x_1508_ = l_Lean_Syntax_node2(v___x_1499_, v___x_1500_, v___x_1505_, v___x_1507_);
if (v_isShared_1494_ == 0)
{
lean_ctor_set(v___x_1493_, 0, v___x_1508_);
v___x_1510_ = v___x_1493_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v___x_1508_);
lean_ctor_set(v_reuseFailAlloc_1511_, 1, v_a_1491_);
v___x_1510_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
return v___x_1510_;
}
}
}
case 2:
{
lean_object* v_presentation_1513_; lean_object* v___x_1514_; lean_object* v_a_1515_; lean_object* v_a_1516_; lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1537_; 
v_presentation_1513_ = lean_ctor_get(v_x_1460_, 0);
lean_inc(v_presentation_1513_);
lean_dec_ref_known(v_x_1460_, 1);
v___x_1514_ = l___private_Std_Time_Notation_0__Std_Time_convertYear(v_presentation_1513_, v_a_1461_, v_a_1462_);
v_a_1515_ = lean_ctor_get(v___x_1514_, 0);
v_a_1516_ = lean_ctor_get(v___x_1514_, 1);
v_isSharedCheck_1537_ = !lean_is_exclusive(v___x_1514_);
if (v_isSharedCheck_1537_ == 0)
{
v___x_1518_ = v___x_1514_;
v_isShared_1519_ = v_isSharedCheck_1537_;
goto v_resetjp_1517_;
}
else
{
lean_inc(v_a_1516_);
lean_inc(v_a_1515_);
lean_dec(v___x_1514_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1537_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
lean_object* v_quotContext_1520_; lean_object* v_currMacroScope_1521_; lean_object* v_ref_1522_; uint8_t v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1535_; 
v_quotContext_1520_ = lean_ctor_get(v_a_1461_, 1);
v_currMacroScope_1521_ = lean_ctor_get(v_a_1461_, 2);
v_ref_1522_ = lean_ctor_get(v_a_1461_, 5);
v___x_1523_ = 0;
v___x_1524_ = l_Lean_SourceInfo_fromRef(v_ref_1522_, v___x_1523_);
v___x_1525_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_1526_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__18, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__18_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__18);
v___x_1527_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__20));
lean_inc(v_currMacroScope_1521_);
lean_inc(v_quotContext_1520_);
v___x_1528_ = l_Lean_addMacroScope(v_quotContext_1520_, v___x_1527_, v_currMacroScope_1521_);
v___x_1529_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__24));
lean_inc_n(v___x_1524_, 2);
v___x_1530_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1530_, 0, v___x_1524_);
lean_ctor_set(v___x_1530_, 1, v___x_1526_);
lean_ctor_set(v___x_1530_, 2, v___x_1528_);
lean_ctor_set(v___x_1530_, 3, v___x_1529_);
v___x_1531_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_1532_ = l_Lean_Syntax_node1(v___x_1524_, v___x_1531_, v_a_1515_);
v___x_1533_ = l_Lean_Syntax_node2(v___x_1524_, v___x_1525_, v___x_1530_, v___x_1532_);
if (v_isShared_1519_ == 0)
{
lean_ctor_set(v___x_1518_, 0, v___x_1533_);
v___x_1535_ = v___x_1518_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v___x_1533_);
lean_ctor_set(v_reuseFailAlloc_1536_, 1, v_a_1516_);
v___x_1535_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
return v___x_1535_;
}
}
}
case 3:
{
lean_object* v_presentation_1538_; lean_object* v___x_1539_; lean_object* v_a_1540_; lean_object* v_a_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1562_; 
v_presentation_1538_ = lean_ctor_get(v_x_1460_, 0);
lean_inc(v_presentation_1538_);
lean_dec_ref_known(v_x_1460_, 1);
v___x_1539_ = l___private_Std_Time_Notation_0__Std_Time_convertYear(v_presentation_1538_, v_a_1461_, v_a_1462_);
v_a_1540_ = lean_ctor_get(v___x_1539_, 0);
v_a_1541_ = lean_ctor_get(v___x_1539_, 1);
v_isSharedCheck_1562_ = !lean_is_exclusive(v___x_1539_);
if (v_isSharedCheck_1562_ == 0)
{
v___x_1543_ = v___x_1539_;
v_isShared_1544_ = v_isSharedCheck_1562_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_a_1541_);
lean_inc(v_a_1540_);
lean_dec(v___x_1539_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1562_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v_quotContext_1545_; lean_object* v_currMacroScope_1546_; lean_object* v_ref_1547_; uint8_t v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1560_; 
v_quotContext_1545_ = lean_ctor_get(v_a_1461_, 1);
v_currMacroScope_1546_ = lean_ctor_get(v_a_1461_, 2);
v_ref_1547_ = lean_ctor_get(v_a_1461_, 5);
v___x_1548_ = 0;
v___x_1549_ = l_Lean_SourceInfo_fromRef(v_ref_1547_, v___x_1548_);
v___x_1550_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_1551_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__26, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__26_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__26);
v___x_1552_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__28));
lean_inc(v_currMacroScope_1546_);
lean_inc(v_quotContext_1545_);
v___x_1553_ = l_Lean_addMacroScope(v_quotContext_1545_, v___x_1552_, v_currMacroScope_1546_);
v___x_1554_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__32));
lean_inc_n(v___x_1549_, 2);
v___x_1555_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1555_, 0, v___x_1549_);
lean_ctor_set(v___x_1555_, 1, v___x_1551_);
lean_ctor_set(v___x_1555_, 2, v___x_1553_);
lean_ctor_set(v___x_1555_, 3, v___x_1554_);
v___x_1556_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_1557_ = l_Lean_Syntax_node1(v___x_1549_, v___x_1556_, v_a_1540_);
v___x_1558_ = l_Lean_Syntax_node2(v___x_1549_, v___x_1550_, v___x_1555_, v___x_1557_);
if (v_isShared_1544_ == 0)
{
lean_ctor_set(v___x_1543_, 0, v___x_1558_);
v___x_1560_ = v___x_1543_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v___x_1558_);
lean_ctor_set(v_reuseFailAlloc_1561_, 1, v_a_1541_);
v___x_1560_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
return v___x_1560_;
}
}
}
case 4:
{
lean_object* v_presentation_1563_; lean_object* v___x_1564_; lean_object* v_a_1565_; lean_object* v_a_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1587_; 
v_presentation_1563_ = lean_ctor_get(v_x_1460_, 0);
lean_inc(v_presentation_1563_);
lean_dec_ref_known(v_x_1460_, 1);
v___x_1564_ = l___private_Std_Time_Notation_0__Std_Time_convertNumber(v_presentation_1563_, v_a_1461_, v_a_1462_);
v_a_1565_ = lean_ctor_get(v___x_1564_, 0);
v_a_1566_ = lean_ctor_get(v___x_1564_, 1);
v_isSharedCheck_1587_ = !lean_is_exclusive(v___x_1564_);
if (v_isSharedCheck_1587_ == 0)
{
v___x_1568_ = v___x_1564_;
v_isShared_1569_ = v_isSharedCheck_1587_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_a_1566_);
lean_inc(v_a_1565_);
lean_dec(v___x_1564_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1587_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
lean_object* v_quotContext_1570_; lean_object* v_currMacroScope_1571_; lean_object* v_ref_1572_; uint8_t v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1585_; 
v_quotContext_1570_ = lean_ctor_get(v_a_1461_, 1);
v_currMacroScope_1571_ = lean_ctor_get(v_a_1461_, 2);
v_ref_1572_ = lean_ctor_get(v_a_1461_, 5);
v___x_1573_ = 0;
v___x_1574_ = l_Lean_SourceInfo_fromRef(v_ref_1572_, v___x_1573_);
v___x_1575_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_1576_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__34, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__34_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__34);
v___x_1577_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__36));
lean_inc(v_currMacroScope_1571_);
lean_inc(v_quotContext_1570_);
v___x_1578_ = l_Lean_addMacroScope(v_quotContext_1570_, v___x_1577_, v_currMacroScope_1571_);
v___x_1579_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__40));
lean_inc_n(v___x_1574_, 2);
v___x_1580_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1580_, 0, v___x_1574_);
lean_ctor_set(v___x_1580_, 1, v___x_1576_);
lean_ctor_set(v___x_1580_, 2, v___x_1578_);
lean_ctor_set(v___x_1580_, 3, v___x_1579_);
v___x_1581_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_1582_ = l_Lean_Syntax_node1(v___x_1574_, v___x_1581_, v_a_1565_);
v___x_1583_ = l_Lean_Syntax_node2(v___x_1574_, v___x_1575_, v___x_1580_, v___x_1582_);
if (v_isShared_1569_ == 0)
{
lean_ctor_set(v___x_1568_, 0, v___x_1583_);
v___x_1585_ = v___x_1568_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v___x_1583_);
lean_ctor_set(v_reuseFailAlloc_1586_, 1, v_a_1566_);
v___x_1585_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
return v___x_1585_;
}
}
}
case 5:
{
lean_object* v_presentation_1588_; 
v_presentation_1588_ = lean_ctor_get(v_x_1460_, 0);
lean_inc_ref(v_presentation_1588_);
lean_dec_ref_known(v_x_1460_, 1);
if (lean_obj_tag(v_presentation_1588_) == 0)
{
lean_object* v_val_1589_; lean_object* v___x_1590_; lean_object* v_a_1591_; lean_object* v_a_1592_; lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1639_; 
v_val_1589_ = lean_ctor_get(v_presentation_1588_, 0);
lean_inc(v_val_1589_);
lean_dec_ref_known(v_presentation_1588_, 1);
v___x_1590_ = l___private_Std_Time_Notation_0__Std_Time_convertNumber(v_val_1589_, v_a_1461_, v_a_1462_);
v_a_1591_ = lean_ctor_get(v___x_1590_, 0);
v_a_1592_ = lean_ctor_get(v___x_1590_, 1);
v_isSharedCheck_1639_ = !lean_is_exclusive(v___x_1590_);
if (v_isSharedCheck_1639_ == 0)
{
v___x_1594_ = v___x_1590_;
v_isShared_1595_ = v_isSharedCheck_1639_;
goto v_resetjp_1593_;
}
else
{
lean_inc(v_a_1592_);
lean_inc(v_a_1591_);
lean_dec(v___x_1590_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1639_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
lean_object* v_quotContext_1596_; lean_object* v_currMacroScope_1597_; lean_object* v_ref_1598_; uint8_t v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1637_; 
v_quotContext_1596_ = lean_ctor_get(v_a_1461_, 1);
v_currMacroScope_1597_ = lean_ctor_get(v_a_1461_, 2);
v_ref_1598_ = lean_ctor_get(v_a_1461_, 5);
v___x_1599_ = 0;
v___x_1600_ = l_Lean_SourceInfo_fromRef(v_ref_1598_, v___x_1599_);
v___x_1601_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_1602_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__42, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__42_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__42);
v___x_1603_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__44));
lean_inc_n(v_currMacroScope_1597_, 3);
lean_inc_n(v_quotContext_1596_, 3);
v___x_1604_ = l_Lean_addMacroScope(v_quotContext_1596_, v___x_1603_, v_currMacroScope_1597_);
v___x_1605_ = lean_box(0);
v___x_1606_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__48));
lean_inc_n(v___x_1600_, 13);
v___x_1607_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1607_, 0, v___x_1600_);
lean_ctor_set(v___x_1607_, 1, v___x_1602_);
lean_ctor_set(v___x_1607_, 2, v___x_1604_);
lean_ctor_set(v___x_1607_, 3, v___x_1606_);
v___x_1608_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_1609_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__50));
v___x_1610_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__52));
v___x_1611_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__53));
v___x_1612_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1612_, 0, v___x_1600_);
lean_ctor_set(v___x_1612_, 1, v___x_1611_);
v___x_1613_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__55));
v___x_1614_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__57, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__57_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__57);
v___x_1615_ = lean_box(0);
v___x_1616_ = l_Lean_addMacroScope(v_quotContext_1596_, v___x_1615_, v_currMacroScope_1597_);
v___x_1617_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__73));
v___x_1618_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1618_, 0, v___x_1600_);
lean_ctor_set(v___x_1618_, 1, v___x_1614_);
lean_ctor_set(v___x_1618_, 2, v___x_1616_);
lean_ctor_set(v___x_1618_, 3, v___x_1617_);
v___x_1619_ = l_Lean_Syntax_node1(v___x_1600_, v___x_1613_, v___x_1618_);
v___x_1620_ = l_Lean_Syntax_node2(v___x_1600_, v___x_1610_, v___x_1612_, v___x_1619_);
v___x_1621_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__75));
v___x_1622_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__76));
v___x_1623_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1623_, 0, v___x_1600_);
lean_ctor_set(v___x_1623_, 1, v___x_1622_);
v___x_1624_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__78, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__78_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__78);
v___x_1625_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__79));
v___x_1626_ = l_Lean_addMacroScope(v_quotContext_1596_, v___x_1625_, v_currMacroScope_1597_);
v___x_1627_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1627_, 0, v___x_1600_);
lean_ctor_set(v___x_1627_, 1, v___x_1624_);
lean_ctor_set(v___x_1627_, 2, v___x_1626_);
lean_ctor_set(v___x_1627_, 3, v___x_1605_);
v___x_1628_ = l_Lean_Syntax_node2(v___x_1600_, v___x_1621_, v___x_1623_, v___x_1627_);
v___x_1629_ = l_Lean_Syntax_node1(v___x_1600_, v___x_1608_, v_a_1591_);
v___x_1630_ = l_Lean_Syntax_node2(v___x_1600_, v___x_1601_, v___x_1628_, v___x_1629_);
v___x_1631_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__80));
v___x_1632_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1600_);
lean_ctor_set(v___x_1632_, 1, v___x_1631_);
v___x_1633_ = l_Lean_Syntax_node3(v___x_1600_, v___x_1609_, v___x_1620_, v___x_1630_, v___x_1632_);
v___x_1634_ = l_Lean_Syntax_node1(v___x_1600_, v___x_1608_, v___x_1633_);
v___x_1635_ = l_Lean_Syntax_node2(v___x_1600_, v___x_1601_, v___x_1607_, v___x_1634_);
if (v_isShared_1595_ == 0)
{
lean_ctor_set(v___x_1594_, 0, v___x_1635_);
v___x_1637_ = v___x_1594_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v___x_1635_);
lean_ctor_set(v_reuseFailAlloc_1638_, 1, v_a_1592_);
v___x_1637_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
return v___x_1637_;
}
}
}
else
{
lean_object* v_val_1640_; uint8_t v___x_1641_; lean_object* v___x_1642_; lean_object* v_a_1643_; lean_object* v_a_1644_; lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1691_; 
v_val_1640_ = lean_ctor_get(v_presentation_1588_, 0);
lean_inc(v_val_1640_);
lean_dec_ref_known(v_presentation_1588_, 1);
v___x_1641_ = lean_unbox(v_val_1640_);
lean_dec(v_val_1640_);
v___x_1642_ = l___private_Std_Time_Notation_0__Std_Time_convertText(v___x_1641_, v_a_1461_, v_a_1462_);
v_a_1643_ = lean_ctor_get(v___x_1642_, 0);
v_a_1644_ = lean_ctor_get(v___x_1642_, 1);
v_isSharedCheck_1691_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1691_ == 0)
{
v___x_1646_ = v___x_1642_;
v_isShared_1647_ = v_isSharedCheck_1691_;
goto v_resetjp_1645_;
}
else
{
lean_inc(v_a_1644_);
lean_inc(v_a_1643_);
lean_dec(v___x_1642_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1691_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
lean_object* v_quotContext_1648_; lean_object* v_currMacroScope_1649_; lean_object* v_ref_1650_; uint8_t v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1689_; 
v_quotContext_1648_ = lean_ctor_get(v_a_1461_, 1);
v_currMacroScope_1649_ = lean_ctor_get(v_a_1461_, 2);
v_ref_1650_ = lean_ctor_get(v_a_1461_, 5);
v___x_1651_ = 0;
v___x_1652_ = l_Lean_SourceInfo_fromRef(v_ref_1650_, v___x_1651_);
v___x_1653_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_1654_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__42, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__42_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__42);
v___x_1655_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__44));
lean_inc_n(v_currMacroScope_1649_, 3);
lean_inc_n(v_quotContext_1648_, 3);
v___x_1656_ = l_Lean_addMacroScope(v_quotContext_1648_, v___x_1655_, v_currMacroScope_1649_);
v___x_1657_ = lean_box(0);
v___x_1658_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__48));
lean_inc_n(v___x_1652_, 13);
v___x_1659_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1659_, 0, v___x_1652_);
lean_ctor_set(v___x_1659_, 1, v___x_1654_);
lean_ctor_set(v___x_1659_, 2, v___x_1656_);
lean_ctor_set(v___x_1659_, 3, v___x_1658_);
v___x_1660_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_1661_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__50));
v___x_1662_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__52));
v___x_1663_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__53));
v___x_1664_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1664_, 0, v___x_1652_);
lean_ctor_set(v___x_1664_, 1, v___x_1663_);
v___x_1665_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__55));
v___x_1666_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__57, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__57_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__57);
v___x_1667_ = lean_box(0);
v___x_1668_ = l_Lean_addMacroScope(v_quotContext_1648_, v___x_1667_, v_currMacroScope_1649_);
v___x_1669_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__73));
v___x_1670_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1670_, 0, v___x_1652_);
lean_ctor_set(v___x_1670_, 1, v___x_1666_);
lean_ctor_set(v___x_1670_, 2, v___x_1668_);
lean_ctor_set(v___x_1670_, 3, v___x_1669_);
v___x_1671_ = l_Lean_Syntax_node1(v___x_1652_, v___x_1665_, v___x_1670_);
v___x_1672_ = l_Lean_Syntax_node2(v___x_1652_, v___x_1662_, v___x_1664_, v___x_1671_);
v___x_1673_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__75));
v___x_1674_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__76));
v___x_1675_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1675_, 0, v___x_1652_);
lean_ctor_set(v___x_1675_, 1, v___x_1674_);
v___x_1676_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__82, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__82_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__82);
v___x_1677_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__83));
v___x_1678_ = l_Lean_addMacroScope(v_quotContext_1648_, v___x_1677_, v_currMacroScope_1649_);
v___x_1679_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1679_, 0, v___x_1652_);
lean_ctor_set(v___x_1679_, 1, v___x_1676_);
lean_ctor_set(v___x_1679_, 2, v___x_1678_);
lean_ctor_set(v___x_1679_, 3, v___x_1657_);
v___x_1680_ = l_Lean_Syntax_node2(v___x_1652_, v___x_1673_, v___x_1675_, v___x_1679_);
v___x_1681_ = l_Lean_Syntax_node1(v___x_1652_, v___x_1660_, v_a_1643_);
v___x_1682_ = l_Lean_Syntax_node2(v___x_1652_, v___x_1653_, v___x_1680_, v___x_1681_);
v___x_1683_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__80));
v___x_1684_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1684_, 0, v___x_1652_);
lean_ctor_set(v___x_1684_, 1, v___x_1683_);
v___x_1685_ = l_Lean_Syntax_node3(v___x_1652_, v___x_1661_, v___x_1672_, v___x_1682_, v___x_1684_);
v___x_1686_ = l_Lean_Syntax_node1(v___x_1652_, v___x_1660_, v___x_1685_);
v___x_1687_ = l_Lean_Syntax_node2(v___x_1652_, v___x_1653_, v___x_1659_, v___x_1686_);
if (v_isShared_1647_ == 0)
{
lean_ctor_set(v___x_1646_, 0, v___x_1687_);
v___x_1689_ = v___x_1646_;
goto v_reusejp_1688_;
}
else
{
lean_object* v_reuseFailAlloc_1690_; 
v_reuseFailAlloc_1690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1690_, 0, v___x_1687_);
lean_ctor_set(v_reuseFailAlloc_1690_, 1, v_a_1644_);
v___x_1689_ = v_reuseFailAlloc_1690_;
goto v_reusejp_1688_;
}
v_reusejp_1688_:
{
return v___x_1689_;
}
}
}
}
case 6:
{
lean_object* v_presentation_1692_; lean_object* v___x_1693_; lean_object* v_a_1694_; lean_object* v_a_1695_; lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1716_; 
v_presentation_1692_ = lean_ctor_get(v_x_1460_, 0);
lean_inc(v_presentation_1692_);
lean_dec_ref_known(v_x_1460_, 1);
v___x_1693_ = l___private_Std_Time_Notation_0__Std_Time_convertNumber(v_presentation_1692_, v_a_1461_, v_a_1462_);
v_a_1694_ = lean_ctor_get(v___x_1693_, 0);
v_a_1695_ = lean_ctor_get(v___x_1693_, 1);
v_isSharedCheck_1716_ = !lean_is_exclusive(v___x_1693_);
if (v_isSharedCheck_1716_ == 0)
{
v___x_1697_ = v___x_1693_;
v_isShared_1698_ = v_isSharedCheck_1716_;
goto v_resetjp_1696_;
}
else
{
lean_inc(v_a_1695_);
lean_inc(v_a_1694_);
lean_dec(v___x_1693_);
v___x_1697_ = lean_box(0);
v_isShared_1698_ = v_isSharedCheck_1716_;
goto v_resetjp_1696_;
}
v_resetjp_1696_:
{
lean_object* v_quotContext_1699_; lean_object* v_currMacroScope_1700_; lean_object* v_ref_1701_; uint8_t v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1714_; 
v_quotContext_1699_ = lean_ctor_get(v_a_1461_, 1);
v_currMacroScope_1700_ = lean_ctor_get(v_a_1461_, 2);
v_ref_1701_ = lean_ctor_get(v_a_1461_, 5);
v___x_1702_ = 0;
v___x_1703_ = l_Lean_SourceInfo_fromRef(v_ref_1701_, v___x_1702_);
v___x_1704_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_1705_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__85, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__85_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__85);
v___x_1706_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__87));
lean_inc(v_currMacroScope_1700_);
lean_inc(v_quotContext_1699_);
v___x_1707_ = l_Lean_addMacroScope(v_quotContext_1699_, v___x_1706_, v_currMacroScope_1700_);
v___x_1708_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__91));
lean_inc_n(v___x_1703_, 2);
v___x_1709_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1709_, 0, v___x_1703_);
lean_ctor_set(v___x_1709_, 1, v___x_1705_);
lean_ctor_set(v___x_1709_, 2, v___x_1707_);
lean_ctor_set(v___x_1709_, 3, v___x_1708_);
v___x_1710_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_1711_ = l_Lean_Syntax_node1(v___x_1703_, v___x_1710_, v_a_1694_);
v___x_1712_ = l_Lean_Syntax_node2(v___x_1703_, v___x_1704_, v___x_1709_, v___x_1711_);
if (v_isShared_1698_ == 0)
{
lean_ctor_set(v___x_1697_, 0, v___x_1712_);
v___x_1714_ = v___x_1697_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1715_; 
v_reuseFailAlloc_1715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1715_, 0, v___x_1712_);
lean_ctor_set(v_reuseFailAlloc_1715_, 1, v_a_1695_);
v___x_1714_ = v_reuseFailAlloc_1715_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
return v___x_1714_;
}
}
}
case 7:
{
lean_object* v_presentation_1717_; 
v_presentation_1717_ = lean_ctor_get(v_x_1460_, 0);
lean_inc_ref(v_presentation_1717_);
lean_dec_ref_known(v_x_1460_, 1);
if (lean_obj_tag(v_presentation_1717_) == 0)
{
lean_object* v_val_1718_; lean_object* v___x_1719_; lean_object* v_a_1720_; lean_object* v_a_1721_; lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1768_; 
v_val_1718_ = lean_ctor_get(v_presentation_1717_, 0);
lean_inc(v_val_1718_);
lean_dec_ref_known(v_presentation_1717_, 1);
v___x_1719_ = l___private_Std_Time_Notation_0__Std_Time_convertNumber(v_val_1718_, v_a_1461_, v_a_1462_);
v_a_1720_ = lean_ctor_get(v___x_1719_, 0);
v_a_1721_ = lean_ctor_get(v___x_1719_, 1);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1719_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1723_ = v___x_1719_;
v_isShared_1724_ = v_isSharedCheck_1768_;
goto v_resetjp_1722_;
}
else
{
lean_inc(v_a_1721_);
lean_inc(v_a_1720_);
lean_dec(v___x_1719_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1768_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
lean_object* v_quotContext_1725_; lean_object* v_currMacroScope_1726_; lean_object* v_ref_1727_; uint8_t v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1766_; 
v_quotContext_1725_ = lean_ctor_get(v_a_1461_, 1);
v_currMacroScope_1726_ = lean_ctor_get(v_a_1461_, 2);
v_ref_1727_ = lean_ctor_get(v_a_1461_, 5);
v___x_1728_ = 0;
v___x_1729_ = l_Lean_SourceInfo_fromRef(v_ref_1727_, v___x_1728_);
v___x_1730_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_1731_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__93, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__93_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__93);
v___x_1732_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__95));
lean_inc_n(v_currMacroScope_1726_, 3);
lean_inc_n(v_quotContext_1725_, 3);
v___x_1733_ = l_Lean_addMacroScope(v_quotContext_1725_, v___x_1732_, v_currMacroScope_1726_);
v___x_1734_ = lean_box(0);
v___x_1735_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__99));
lean_inc_n(v___x_1729_, 13);
v___x_1736_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1736_, 0, v___x_1729_);
lean_ctor_set(v___x_1736_, 1, v___x_1731_);
lean_ctor_set(v___x_1736_, 2, v___x_1733_);
lean_ctor_set(v___x_1736_, 3, v___x_1735_);
v___x_1737_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_1738_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__50));
v___x_1739_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__52));
v___x_1740_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__53));
v___x_1741_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1741_, 0, v___x_1729_);
lean_ctor_set(v___x_1741_, 1, v___x_1740_);
v___x_1742_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__55));
v___x_1743_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__57, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__57_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__57);
v___x_1744_ = lean_box(0);
v___x_1745_ = l_Lean_addMacroScope(v_quotContext_1725_, v___x_1744_, v_currMacroScope_1726_);
v___x_1746_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__73));
v___x_1747_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1747_, 0, v___x_1729_);
lean_ctor_set(v___x_1747_, 1, v___x_1743_);
lean_ctor_set(v___x_1747_, 2, v___x_1745_);
lean_ctor_set(v___x_1747_, 3, v___x_1746_);
v___x_1748_ = l_Lean_Syntax_node1(v___x_1729_, v___x_1742_, v___x_1747_);
v___x_1749_ = l_Lean_Syntax_node2(v___x_1729_, v___x_1739_, v___x_1741_, v___x_1748_);
v___x_1750_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__75));
v___x_1751_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__76));
v___x_1752_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1752_, 0, v___x_1729_);
lean_ctor_set(v___x_1752_, 1, v___x_1751_);
v___x_1753_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__78, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__78_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__78);
v___x_1754_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__79));
v___x_1755_ = l_Lean_addMacroScope(v_quotContext_1725_, v___x_1754_, v_currMacroScope_1726_);
v___x_1756_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1756_, 0, v___x_1729_);
lean_ctor_set(v___x_1756_, 1, v___x_1753_);
lean_ctor_set(v___x_1756_, 2, v___x_1755_);
lean_ctor_set(v___x_1756_, 3, v___x_1734_);
v___x_1757_ = l_Lean_Syntax_node2(v___x_1729_, v___x_1750_, v___x_1752_, v___x_1756_);
v___x_1758_ = l_Lean_Syntax_node1(v___x_1729_, v___x_1737_, v_a_1720_);
v___x_1759_ = l_Lean_Syntax_node2(v___x_1729_, v___x_1730_, v___x_1757_, v___x_1758_);
v___x_1760_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__80));
v___x_1761_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1761_, 0, v___x_1729_);
lean_ctor_set(v___x_1761_, 1, v___x_1760_);
v___x_1762_ = l_Lean_Syntax_node3(v___x_1729_, v___x_1738_, v___x_1749_, v___x_1759_, v___x_1761_);
v___x_1763_ = l_Lean_Syntax_node1(v___x_1729_, v___x_1737_, v___x_1762_);
v___x_1764_ = l_Lean_Syntax_node2(v___x_1729_, v___x_1730_, v___x_1736_, v___x_1763_);
if (v_isShared_1724_ == 0)
{
lean_ctor_set(v___x_1723_, 0, v___x_1764_);
v___x_1766_ = v___x_1723_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v___x_1764_);
lean_ctor_set(v_reuseFailAlloc_1767_, 1, v_a_1721_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
return v___x_1766_;
}
}
}
else
{
lean_object* v_val_1769_; uint8_t v___x_1770_; lean_object* v___x_1771_; lean_object* v_a_1772_; lean_object* v_a_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1820_; 
v_val_1769_ = lean_ctor_get(v_presentation_1717_, 0);
lean_inc(v_val_1769_);
lean_dec_ref_known(v_presentation_1717_, 1);
v___x_1770_ = lean_unbox(v_val_1769_);
lean_dec(v_val_1769_);
v___x_1771_ = l___private_Std_Time_Notation_0__Std_Time_convertText(v___x_1770_, v_a_1461_, v_a_1462_);
v_a_1772_ = lean_ctor_get(v___x_1771_, 0);
v_a_1773_ = lean_ctor_get(v___x_1771_, 1);
v_isSharedCheck_1820_ = !lean_is_exclusive(v___x_1771_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1775_ = v___x_1771_;
v_isShared_1776_ = v_isSharedCheck_1820_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_a_1773_);
lean_inc(v_a_1772_);
lean_dec(v___x_1771_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1820_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v_quotContext_1777_; lean_object* v_currMacroScope_1778_; lean_object* v_ref_1779_; uint8_t v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1818_; 
v_quotContext_1777_ = lean_ctor_get(v_a_1461_, 1);
v_currMacroScope_1778_ = lean_ctor_get(v_a_1461_, 2);
v_ref_1779_ = lean_ctor_get(v_a_1461_, 5);
v___x_1780_ = 0;
v___x_1781_ = l_Lean_SourceInfo_fromRef(v_ref_1779_, v___x_1780_);
v___x_1782_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_1783_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__93, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__93_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__93);
v___x_1784_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__95));
lean_inc_n(v_currMacroScope_1778_, 3);
lean_inc_n(v_quotContext_1777_, 3);
v___x_1785_ = l_Lean_addMacroScope(v_quotContext_1777_, v___x_1784_, v_currMacroScope_1778_);
v___x_1786_ = lean_box(0);
v___x_1787_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__99));
lean_inc_n(v___x_1781_, 13);
v___x_1788_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1788_, 0, v___x_1781_);
lean_ctor_set(v___x_1788_, 1, v___x_1783_);
lean_ctor_set(v___x_1788_, 2, v___x_1785_);
lean_ctor_set(v___x_1788_, 3, v___x_1787_);
v___x_1789_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_1790_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__50));
v___x_1791_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__52));
v___x_1792_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__53));
v___x_1793_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1793_, 0, v___x_1781_);
lean_ctor_set(v___x_1793_, 1, v___x_1792_);
v___x_1794_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__55));
v___x_1795_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__57, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__57_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__57);
v___x_1796_ = lean_box(0);
v___x_1797_ = l_Lean_addMacroScope(v_quotContext_1777_, v___x_1796_, v_currMacroScope_1778_);
v___x_1798_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__73));
v___x_1799_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1799_, 0, v___x_1781_);
lean_ctor_set(v___x_1799_, 1, v___x_1795_);
lean_ctor_set(v___x_1799_, 2, v___x_1797_);
lean_ctor_set(v___x_1799_, 3, v___x_1798_);
v___x_1800_ = l_Lean_Syntax_node1(v___x_1781_, v___x_1794_, v___x_1799_);
v___x_1801_ = l_Lean_Syntax_node2(v___x_1781_, v___x_1791_, v___x_1793_, v___x_1800_);
v___x_1802_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__75));
v___x_1803_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__76));
v___x_1804_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1804_, 0, v___x_1781_);
lean_ctor_set(v___x_1804_, 1, v___x_1803_);
v___x_1805_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__82, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__82_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__82);
v___x_1806_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__83));
v___x_1807_ = l_Lean_addMacroScope(v_quotContext_1777_, v___x_1806_, v_currMacroScope_1778_);
v___x_1808_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1808_, 0, v___x_1781_);
lean_ctor_set(v___x_1808_, 1, v___x_1805_);
lean_ctor_set(v___x_1808_, 2, v___x_1807_);
lean_ctor_set(v___x_1808_, 3, v___x_1786_);
v___x_1809_ = l_Lean_Syntax_node2(v___x_1781_, v___x_1802_, v___x_1804_, v___x_1808_);
v___x_1810_ = l_Lean_Syntax_node1(v___x_1781_, v___x_1789_, v_a_1772_);
v___x_1811_ = l_Lean_Syntax_node2(v___x_1781_, v___x_1782_, v___x_1809_, v___x_1810_);
v___x_1812_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__80));
v___x_1813_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1813_, 0, v___x_1781_);
lean_ctor_set(v___x_1813_, 1, v___x_1812_);
v___x_1814_ = l_Lean_Syntax_node3(v___x_1781_, v___x_1790_, v___x_1801_, v___x_1811_, v___x_1813_);
v___x_1815_ = l_Lean_Syntax_node1(v___x_1781_, v___x_1789_, v___x_1814_);
v___x_1816_ = l_Lean_Syntax_node2(v___x_1781_, v___x_1782_, v___x_1788_, v___x_1815_);
if (v_isShared_1776_ == 0)
{
lean_ctor_set(v___x_1775_, 0, v___x_1816_);
v___x_1818_ = v___x_1775_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v___x_1816_);
lean_ctor_set(v_reuseFailAlloc_1819_, 1, v_a_1773_);
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
case 8:
{
lean_object* v_presentation_1821_; lean_object* v___x_1822_; lean_object* v_a_1823_; lean_object* v_a_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1845_; 
v_presentation_1821_ = lean_ctor_get(v_x_1460_, 0);
lean_inc(v_presentation_1821_);
lean_dec_ref_known(v_x_1460_, 1);
v___x_1822_ = l___private_Std_Time_Notation_0__Std_Time_convertNumber(v_presentation_1821_, v_a_1461_, v_a_1462_);
v_a_1823_ = lean_ctor_get(v___x_1822_, 0);
v_a_1824_ = lean_ctor_get(v___x_1822_, 1);
v_isSharedCheck_1845_ = !lean_is_exclusive(v___x_1822_);
if (v_isSharedCheck_1845_ == 0)
{
v___x_1826_ = v___x_1822_;
v_isShared_1827_ = v_isSharedCheck_1845_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_a_1824_);
lean_inc(v_a_1823_);
lean_dec(v___x_1822_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1845_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v_quotContext_1828_; lean_object* v_currMacroScope_1829_; lean_object* v_ref_1830_; uint8_t v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1843_; 
v_quotContext_1828_ = lean_ctor_get(v_a_1461_, 1);
v_currMacroScope_1829_ = lean_ctor_get(v_a_1461_, 2);
v_ref_1830_ = lean_ctor_get(v_a_1461_, 5);
v___x_1831_ = 0;
v___x_1832_ = l_Lean_SourceInfo_fromRef(v_ref_1830_, v___x_1831_);
v___x_1833_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_1834_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__101, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__101_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__101);
v___x_1835_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__103));
lean_inc(v_currMacroScope_1829_);
lean_inc(v_quotContext_1828_);
v___x_1836_ = l_Lean_addMacroScope(v_quotContext_1828_, v___x_1835_, v_currMacroScope_1829_);
v___x_1837_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__107));
lean_inc_n(v___x_1832_, 2);
v___x_1838_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1838_, 0, v___x_1832_);
lean_ctor_set(v___x_1838_, 1, v___x_1834_);
lean_ctor_set(v___x_1838_, 2, v___x_1836_);
lean_ctor_set(v___x_1838_, 3, v___x_1837_);
v___x_1839_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_1840_ = l_Lean_Syntax_node1(v___x_1832_, v___x_1839_, v_a_1823_);
v___x_1841_ = l_Lean_Syntax_node2(v___x_1832_, v___x_1833_, v___x_1838_, v___x_1840_);
if (v_isShared_1827_ == 0)
{
lean_ctor_set(v___x_1826_, 0, v___x_1841_);
v___x_1843_ = v___x_1826_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v___x_1841_);
lean_ctor_set(v_reuseFailAlloc_1844_, 1, v_a_1824_);
v___x_1843_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
return v___x_1843_;
}
}
}
case 9:
{
lean_object* v_presentation_1846_; lean_object* v___x_1847_; lean_object* v_a_1848_; lean_object* v_a_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1870_; 
v_presentation_1846_ = lean_ctor_get(v_x_1460_, 0);
lean_inc(v_presentation_1846_);
lean_dec_ref_known(v_x_1460_, 1);
v___x_1847_ = l___private_Std_Time_Notation_0__Std_Time_convertNumber(v_presentation_1846_, v_a_1461_, v_a_1462_);
v_a_1848_ = lean_ctor_get(v___x_1847_, 0);
v_a_1849_ = lean_ctor_get(v___x_1847_, 1);
v_isSharedCheck_1870_ = !lean_is_exclusive(v___x_1847_);
if (v_isSharedCheck_1870_ == 0)
{
v___x_1851_ = v___x_1847_;
v_isShared_1852_ = v_isSharedCheck_1870_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_a_1849_);
lean_inc(v_a_1848_);
lean_dec(v___x_1847_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1870_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
lean_object* v_quotContext_1853_; lean_object* v_currMacroScope_1854_; lean_object* v_ref_1855_; uint8_t v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1868_; 
v_quotContext_1853_ = lean_ctor_get(v_a_1461_, 1);
v_currMacroScope_1854_ = lean_ctor_get(v_a_1461_, 2);
v_ref_1855_ = lean_ctor_get(v_a_1461_, 5);
v___x_1856_ = 0;
v___x_1857_ = l_Lean_SourceInfo_fromRef(v_ref_1855_, v___x_1856_);
v___x_1858_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_1859_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__109, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__109_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__109);
v___x_1860_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__111));
lean_inc(v_currMacroScope_1854_);
lean_inc(v_quotContext_1853_);
v___x_1861_ = l_Lean_addMacroScope(v_quotContext_1853_, v___x_1860_, v_currMacroScope_1854_);
v___x_1862_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__115));
lean_inc_n(v___x_1857_, 2);
v___x_1863_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1863_, 0, v___x_1857_);
lean_ctor_set(v___x_1863_, 1, v___x_1859_);
lean_ctor_set(v___x_1863_, 2, v___x_1861_);
lean_ctor_set(v___x_1863_, 3, v___x_1862_);
v___x_1864_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_1865_ = l_Lean_Syntax_node1(v___x_1857_, v___x_1864_, v_a_1848_);
v___x_1866_ = l_Lean_Syntax_node2(v___x_1857_, v___x_1858_, v___x_1863_, v___x_1865_);
if (v_isShared_1852_ == 0)
{
lean_ctor_set(v___x_1851_, 0, v___x_1866_);
v___x_1868_ = v___x_1851_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1869_; 
v_reuseFailAlloc_1869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1869_, 0, v___x_1866_);
lean_ctor_set(v_reuseFailAlloc_1869_, 1, v_a_1849_);
v___x_1868_ = v_reuseFailAlloc_1869_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
return v___x_1868_;
}
}
}
case 10:
{
uint8_t v_presentation_1871_; lean_object* v___x_1872_; lean_object* v_a_1873_; lean_object* v_a_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1895_; 
v_presentation_1871_ = lean_ctor_get_uint8(v_x_1460_, 0);
lean_dec_ref_known(v_x_1460_, 0);
v___x_1872_ = l___private_Std_Time_Notation_0__Std_Time_convertText(v_presentation_1871_, v_a_1461_, v_a_1462_);
v_a_1873_ = lean_ctor_get(v___x_1872_, 0);
v_a_1874_ = lean_ctor_get(v___x_1872_, 1);
v_isSharedCheck_1895_ = !lean_is_exclusive(v___x_1872_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1876_ = v___x_1872_;
v_isShared_1877_ = v_isSharedCheck_1895_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_a_1874_);
lean_inc(v_a_1873_);
lean_dec(v___x_1872_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1895_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v_quotContext_1878_; lean_object* v_currMacroScope_1879_; lean_object* v_ref_1880_; uint8_t v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1893_; 
v_quotContext_1878_ = lean_ctor_get(v_a_1461_, 1);
v_currMacroScope_1879_ = lean_ctor_get(v_a_1461_, 2);
v_ref_1880_ = lean_ctor_get(v_a_1461_, 5);
v___x_1881_ = 0;
v___x_1882_ = l_Lean_SourceInfo_fromRef(v_ref_1880_, v___x_1881_);
v___x_1883_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_1884_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__117, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__117_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__117);
v___x_1885_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__119));
lean_inc(v_currMacroScope_1879_);
lean_inc(v_quotContext_1878_);
v___x_1886_ = l_Lean_addMacroScope(v_quotContext_1878_, v___x_1885_, v_currMacroScope_1879_);
v___x_1887_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__123));
lean_inc_n(v___x_1882_, 2);
v___x_1888_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1888_, 0, v___x_1882_);
lean_ctor_set(v___x_1888_, 1, v___x_1884_);
lean_ctor_set(v___x_1888_, 2, v___x_1886_);
lean_ctor_set(v___x_1888_, 3, v___x_1887_);
v___x_1889_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_1890_ = l_Lean_Syntax_node1(v___x_1882_, v___x_1889_, v_a_1873_);
v___x_1891_ = l_Lean_Syntax_node2(v___x_1882_, v___x_1883_, v___x_1888_, v___x_1890_);
if (v_isShared_1877_ == 0)
{
lean_ctor_set(v___x_1876_, 0, v___x_1891_);
v___x_1893_ = v___x_1876_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v___x_1891_);
lean_ctor_set(v_reuseFailAlloc_1894_, 1, v_a_1874_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
return v___x_1893_;
}
}
}
case 11:
{
lean_object* v_presentation_1896_; 
v_presentation_1896_ = lean_ctor_get(v_x_1460_, 0);
lean_inc_ref(v_presentation_1896_);
lean_dec_ref_known(v_x_1460_, 1);
if (lean_obj_tag(v_presentation_1896_) == 0)
{
lean_object* v_val_1897_; lean_object* v___x_1898_; lean_object* v_a_1899_; lean_object* v_a_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1947_; 
v_val_1897_ = lean_ctor_get(v_presentation_1896_, 0);
lean_inc(v_val_1897_);
lean_dec_ref_known(v_presentation_1896_, 1);
v___x_1898_ = l___private_Std_Time_Notation_0__Std_Time_convertNumber(v_val_1897_, v_a_1461_, v_a_1462_);
v_a_1899_ = lean_ctor_get(v___x_1898_, 0);
v_a_1900_ = lean_ctor_get(v___x_1898_, 1);
v_isSharedCheck_1947_ = !lean_is_exclusive(v___x_1898_);
if (v_isSharedCheck_1947_ == 0)
{
v___x_1902_ = v___x_1898_;
v_isShared_1903_ = v_isSharedCheck_1947_;
goto v_resetjp_1901_;
}
else
{
lean_inc(v_a_1900_);
lean_inc(v_a_1899_);
lean_dec(v___x_1898_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1947_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
lean_object* v_quotContext_1904_; lean_object* v_currMacroScope_1905_; lean_object* v_ref_1906_; uint8_t v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1945_; 
v_quotContext_1904_ = lean_ctor_get(v_a_1461_, 1);
v_currMacroScope_1905_ = lean_ctor_get(v_a_1461_, 2);
v_ref_1906_ = lean_ctor_get(v_a_1461_, 5);
v___x_1907_ = 0;
v___x_1908_ = l_Lean_SourceInfo_fromRef(v_ref_1906_, v___x_1907_);
v___x_1909_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_1910_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__125, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__125_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__125);
v___x_1911_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__127));
lean_inc_n(v_currMacroScope_1905_, 3);
lean_inc_n(v_quotContext_1904_, 3);
v___x_1912_ = l_Lean_addMacroScope(v_quotContext_1904_, v___x_1911_, v_currMacroScope_1905_);
v___x_1913_ = lean_box(0);
v___x_1914_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__131));
lean_inc_n(v___x_1908_, 13);
v___x_1915_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1915_, 0, v___x_1908_);
lean_ctor_set(v___x_1915_, 1, v___x_1910_);
lean_ctor_set(v___x_1915_, 2, v___x_1912_);
lean_ctor_set(v___x_1915_, 3, v___x_1914_);
v___x_1916_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_1917_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__50));
v___x_1918_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__52));
v___x_1919_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__53));
v___x_1920_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1920_, 0, v___x_1908_);
lean_ctor_set(v___x_1920_, 1, v___x_1919_);
v___x_1921_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__55));
v___x_1922_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__57, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__57_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__57);
v___x_1923_ = lean_box(0);
v___x_1924_ = l_Lean_addMacroScope(v_quotContext_1904_, v___x_1923_, v_currMacroScope_1905_);
v___x_1925_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__73));
v___x_1926_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1926_, 0, v___x_1908_);
lean_ctor_set(v___x_1926_, 1, v___x_1922_);
lean_ctor_set(v___x_1926_, 2, v___x_1924_);
lean_ctor_set(v___x_1926_, 3, v___x_1925_);
v___x_1927_ = l_Lean_Syntax_node1(v___x_1908_, v___x_1921_, v___x_1926_);
v___x_1928_ = l_Lean_Syntax_node2(v___x_1908_, v___x_1918_, v___x_1920_, v___x_1927_);
v___x_1929_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__75));
v___x_1930_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__76));
v___x_1931_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1931_, 0, v___x_1908_);
lean_ctor_set(v___x_1931_, 1, v___x_1930_);
v___x_1932_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__78, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__78_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__78);
v___x_1933_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__79));
v___x_1934_ = l_Lean_addMacroScope(v_quotContext_1904_, v___x_1933_, v_currMacroScope_1905_);
v___x_1935_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1935_, 0, v___x_1908_);
lean_ctor_set(v___x_1935_, 1, v___x_1932_);
lean_ctor_set(v___x_1935_, 2, v___x_1934_);
lean_ctor_set(v___x_1935_, 3, v___x_1913_);
v___x_1936_ = l_Lean_Syntax_node2(v___x_1908_, v___x_1929_, v___x_1931_, v___x_1935_);
v___x_1937_ = l_Lean_Syntax_node1(v___x_1908_, v___x_1916_, v_a_1899_);
v___x_1938_ = l_Lean_Syntax_node2(v___x_1908_, v___x_1909_, v___x_1936_, v___x_1937_);
v___x_1939_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__80));
v___x_1940_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1940_, 0, v___x_1908_);
lean_ctor_set(v___x_1940_, 1, v___x_1939_);
v___x_1941_ = l_Lean_Syntax_node3(v___x_1908_, v___x_1917_, v___x_1928_, v___x_1938_, v___x_1940_);
v___x_1942_ = l_Lean_Syntax_node1(v___x_1908_, v___x_1916_, v___x_1941_);
v___x_1943_ = l_Lean_Syntax_node2(v___x_1908_, v___x_1909_, v___x_1915_, v___x_1942_);
if (v_isShared_1903_ == 0)
{
lean_ctor_set(v___x_1902_, 0, v___x_1943_);
v___x_1945_ = v___x_1902_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v___x_1943_);
lean_ctor_set(v_reuseFailAlloc_1946_, 1, v_a_1900_);
v___x_1945_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
return v___x_1945_;
}
}
}
else
{
lean_object* v_val_1948_; uint8_t v___x_1949_; lean_object* v___x_1950_; lean_object* v_a_1951_; lean_object* v_a_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1999_; 
v_val_1948_ = lean_ctor_get(v_presentation_1896_, 0);
lean_inc(v_val_1948_);
lean_dec_ref_known(v_presentation_1896_, 1);
v___x_1949_ = lean_unbox(v_val_1948_);
lean_dec(v_val_1948_);
v___x_1950_ = l___private_Std_Time_Notation_0__Std_Time_convertText(v___x_1949_, v_a_1461_, v_a_1462_);
v_a_1951_ = lean_ctor_get(v___x_1950_, 0);
v_a_1952_ = lean_ctor_get(v___x_1950_, 1);
v_isSharedCheck_1999_ = !lean_is_exclusive(v___x_1950_);
if (v_isSharedCheck_1999_ == 0)
{
v___x_1954_ = v___x_1950_;
v_isShared_1955_ = v_isSharedCheck_1999_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_a_1952_);
lean_inc(v_a_1951_);
lean_dec(v___x_1950_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1999_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v_quotContext_1956_; lean_object* v_currMacroScope_1957_; lean_object* v_ref_1958_; uint8_t v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1997_; 
v_quotContext_1956_ = lean_ctor_get(v_a_1461_, 1);
v_currMacroScope_1957_ = lean_ctor_get(v_a_1461_, 2);
v_ref_1958_ = lean_ctor_get(v_a_1461_, 5);
v___x_1959_ = 0;
v___x_1960_ = l_Lean_SourceInfo_fromRef(v_ref_1958_, v___x_1959_);
v___x_1961_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_1962_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__125, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__125_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__125);
v___x_1963_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__127));
lean_inc_n(v_currMacroScope_1957_, 3);
lean_inc_n(v_quotContext_1956_, 3);
v___x_1964_ = l_Lean_addMacroScope(v_quotContext_1956_, v___x_1963_, v_currMacroScope_1957_);
v___x_1965_ = lean_box(0);
v___x_1966_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__131));
lean_inc_n(v___x_1960_, 13);
v___x_1967_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1967_, 0, v___x_1960_);
lean_ctor_set(v___x_1967_, 1, v___x_1962_);
lean_ctor_set(v___x_1967_, 2, v___x_1964_);
lean_ctor_set(v___x_1967_, 3, v___x_1966_);
v___x_1968_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_1969_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__50));
v___x_1970_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__52));
v___x_1971_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__53));
v___x_1972_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1972_, 0, v___x_1960_);
lean_ctor_set(v___x_1972_, 1, v___x_1971_);
v___x_1973_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__55));
v___x_1974_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__57, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__57_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__57);
v___x_1975_ = lean_box(0);
v___x_1976_ = l_Lean_addMacroScope(v_quotContext_1956_, v___x_1975_, v_currMacroScope_1957_);
v___x_1977_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__73));
v___x_1978_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1978_, 0, v___x_1960_);
lean_ctor_set(v___x_1978_, 1, v___x_1974_);
lean_ctor_set(v___x_1978_, 2, v___x_1976_);
lean_ctor_set(v___x_1978_, 3, v___x_1977_);
v___x_1979_ = l_Lean_Syntax_node1(v___x_1960_, v___x_1973_, v___x_1978_);
v___x_1980_ = l_Lean_Syntax_node2(v___x_1960_, v___x_1970_, v___x_1972_, v___x_1979_);
v___x_1981_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__75));
v___x_1982_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__76));
v___x_1983_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1983_, 0, v___x_1960_);
lean_ctor_set(v___x_1983_, 1, v___x_1982_);
v___x_1984_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__82, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__82_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__82);
v___x_1985_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__83));
v___x_1986_ = l_Lean_addMacroScope(v_quotContext_1956_, v___x_1985_, v_currMacroScope_1957_);
v___x_1987_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1987_, 0, v___x_1960_);
lean_ctor_set(v___x_1987_, 1, v___x_1984_);
lean_ctor_set(v___x_1987_, 2, v___x_1986_);
lean_ctor_set(v___x_1987_, 3, v___x_1965_);
v___x_1988_ = l_Lean_Syntax_node2(v___x_1960_, v___x_1981_, v___x_1983_, v___x_1987_);
v___x_1989_ = l_Lean_Syntax_node1(v___x_1960_, v___x_1968_, v_a_1951_);
v___x_1990_ = l_Lean_Syntax_node2(v___x_1960_, v___x_1961_, v___x_1988_, v___x_1989_);
v___x_1991_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__80));
v___x_1992_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1992_, 0, v___x_1960_);
lean_ctor_set(v___x_1992_, 1, v___x_1991_);
v___x_1993_ = l_Lean_Syntax_node3(v___x_1960_, v___x_1969_, v___x_1980_, v___x_1990_, v___x_1992_);
v___x_1994_ = l_Lean_Syntax_node1(v___x_1960_, v___x_1968_, v___x_1993_);
v___x_1995_ = l_Lean_Syntax_node2(v___x_1960_, v___x_1961_, v___x_1967_, v___x_1994_);
if (v_isShared_1955_ == 0)
{
lean_ctor_set(v___x_1954_, 0, v___x_1995_);
v___x_1997_ = v___x_1954_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v___x_1995_);
lean_ctor_set(v_reuseFailAlloc_1998_, 1, v_a_1952_);
v___x_1997_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
return v___x_1997_;
}
}
}
}
case 12:
{
lean_object* v_presentation_2000_; lean_object* v___x_2001_; lean_object* v_a_2002_; lean_object* v_a_2003_; lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2024_; 
v_presentation_2000_ = lean_ctor_get(v_x_1460_, 0);
lean_inc(v_presentation_2000_);
lean_dec_ref_known(v_x_1460_, 1);
v___x_2001_ = l___private_Std_Time_Notation_0__Std_Time_convertNumber(v_presentation_2000_, v_a_1461_, v_a_1462_);
v_a_2002_ = lean_ctor_get(v___x_2001_, 0);
v_a_2003_ = lean_ctor_get(v___x_2001_, 1);
v_isSharedCheck_2024_ = !lean_is_exclusive(v___x_2001_);
if (v_isSharedCheck_2024_ == 0)
{
v___x_2005_ = v___x_2001_;
v_isShared_2006_ = v_isSharedCheck_2024_;
goto v_resetjp_2004_;
}
else
{
lean_inc(v_a_2003_);
lean_inc(v_a_2002_);
lean_dec(v___x_2001_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2024_;
goto v_resetjp_2004_;
}
v_resetjp_2004_:
{
lean_object* v_quotContext_2007_; lean_object* v_currMacroScope_2008_; lean_object* v_ref_2009_; uint8_t v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2022_; 
v_quotContext_2007_ = lean_ctor_get(v_a_1461_, 1);
v_currMacroScope_2008_ = lean_ctor_get(v_a_1461_, 2);
v_ref_2009_ = lean_ctor_get(v_a_1461_, 5);
v___x_2010_ = 0;
v___x_2011_ = l_Lean_SourceInfo_fromRef(v_ref_2009_, v___x_2010_);
v___x_2012_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2013_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__133, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__133_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__133);
v___x_2014_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__135));
lean_inc(v_currMacroScope_2008_);
lean_inc(v_quotContext_2007_);
v___x_2015_ = l_Lean_addMacroScope(v_quotContext_2007_, v___x_2014_, v_currMacroScope_2008_);
v___x_2016_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__139));
lean_inc_n(v___x_2011_, 2);
v___x_2017_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2017_, 0, v___x_2011_);
lean_ctor_set(v___x_2017_, 1, v___x_2013_);
lean_ctor_set(v___x_2017_, 2, v___x_2015_);
lean_ctor_set(v___x_2017_, 3, v___x_2016_);
v___x_2018_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2019_ = l_Lean_Syntax_node1(v___x_2011_, v___x_2018_, v_a_2002_);
v___x_2020_ = l_Lean_Syntax_node2(v___x_2011_, v___x_2012_, v___x_2017_, v___x_2019_);
if (v_isShared_2006_ == 0)
{
lean_ctor_set(v___x_2005_, 0, v___x_2020_);
v___x_2022_ = v___x_2005_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v___x_2020_);
lean_ctor_set(v_reuseFailAlloc_2023_, 1, v_a_2003_);
v___x_2022_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
return v___x_2022_;
}
}
}
case 13:
{
uint8_t v_presentation_2025_; lean_object* v___x_2026_; lean_object* v_a_2027_; lean_object* v_a_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2049_; 
v_presentation_2025_ = lean_ctor_get_uint8(v_x_1460_, 0);
lean_dec_ref_known(v_x_1460_, 0);
v___x_2026_ = l___private_Std_Time_Notation_0__Std_Time_convertText(v_presentation_2025_, v_a_1461_, v_a_1462_);
v_a_2027_ = lean_ctor_get(v___x_2026_, 0);
v_a_2028_ = lean_ctor_get(v___x_2026_, 1);
v_isSharedCheck_2049_ = !lean_is_exclusive(v___x_2026_);
if (v_isSharedCheck_2049_ == 0)
{
v___x_2030_ = v___x_2026_;
v_isShared_2031_ = v_isSharedCheck_2049_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_a_2028_);
lean_inc(v_a_2027_);
lean_dec(v___x_2026_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2049_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v_quotContext_2032_; lean_object* v_currMacroScope_2033_; lean_object* v_ref_2034_; uint8_t v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2047_; 
v_quotContext_2032_ = lean_ctor_get(v_a_1461_, 1);
v_currMacroScope_2033_ = lean_ctor_get(v_a_1461_, 2);
v_ref_2034_ = lean_ctor_get(v_a_1461_, 5);
v___x_2035_ = 0;
v___x_2036_ = l_Lean_SourceInfo_fromRef(v_ref_2034_, v___x_2035_);
v___x_2037_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2038_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__141, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__141_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__141);
v___x_2039_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__143));
lean_inc(v_currMacroScope_2033_);
lean_inc(v_quotContext_2032_);
v___x_2040_ = l_Lean_addMacroScope(v_quotContext_2032_, v___x_2039_, v_currMacroScope_2033_);
v___x_2041_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__147));
lean_inc_n(v___x_2036_, 2);
v___x_2042_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2042_, 0, v___x_2036_);
lean_ctor_set(v___x_2042_, 1, v___x_2038_);
lean_ctor_set(v___x_2042_, 2, v___x_2040_);
lean_ctor_set(v___x_2042_, 3, v___x_2041_);
v___x_2043_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2044_ = l_Lean_Syntax_node1(v___x_2036_, v___x_2043_, v_a_2027_);
v___x_2045_ = l_Lean_Syntax_node2(v___x_2036_, v___x_2037_, v___x_2042_, v___x_2044_);
if (v_isShared_2031_ == 0)
{
lean_ctor_set(v___x_2030_, 0, v___x_2045_);
v___x_2047_ = v___x_2030_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v___x_2045_);
lean_ctor_set(v_reuseFailAlloc_2048_, 1, v_a_2028_);
v___x_2047_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
return v___x_2047_;
}
}
}
case 14:
{
lean_object* v_presentation_2050_; lean_object* v___x_2051_; lean_object* v_a_2052_; lean_object* v_a_2053_; lean_object* v___x_2055_; uint8_t v_isShared_2056_; uint8_t v_isSharedCheck_2074_; 
v_presentation_2050_ = lean_ctor_get(v_x_1460_, 0);
lean_inc(v_presentation_2050_);
lean_dec_ref_known(v_x_1460_, 1);
v___x_2051_ = l___private_Std_Time_Notation_0__Std_Time_convertNumber(v_presentation_2050_, v_a_1461_, v_a_1462_);
v_a_2052_ = lean_ctor_get(v___x_2051_, 0);
v_a_2053_ = lean_ctor_get(v___x_2051_, 1);
v_isSharedCheck_2074_ = !lean_is_exclusive(v___x_2051_);
if (v_isSharedCheck_2074_ == 0)
{
v___x_2055_ = v___x_2051_;
v_isShared_2056_ = v_isSharedCheck_2074_;
goto v_resetjp_2054_;
}
else
{
lean_inc(v_a_2053_);
lean_inc(v_a_2052_);
lean_dec(v___x_2051_);
v___x_2055_ = lean_box(0);
v_isShared_2056_ = v_isSharedCheck_2074_;
goto v_resetjp_2054_;
}
v_resetjp_2054_:
{
lean_object* v_quotContext_2057_; lean_object* v_currMacroScope_2058_; lean_object* v_ref_2059_; uint8_t v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2072_; 
v_quotContext_2057_ = lean_ctor_get(v_a_1461_, 1);
v_currMacroScope_2058_ = lean_ctor_get(v_a_1461_, 2);
v_ref_2059_ = lean_ctor_get(v_a_1461_, 5);
v___x_2060_ = 0;
v___x_2061_ = l_Lean_SourceInfo_fromRef(v_ref_2059_, v___x_2060_);
v___x_2062_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2063_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__149, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__149_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__149);
v___x_2064_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__151));
lean_inc(v_currMacroScope_2058_);
lean_inc(v_quotContext_2057_);
v___x_2065_ = l_Lean_addMacroScope(v_quotContext_2057_, v___x_2064_, v_currMacroScope_2058_);
v___x_2066_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__155));
lean_inc_n(v___x_2061_, 2);
v___x_2067_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2067_, 0, v___x_2061_);
lean_ctor_set(v___x_2067_, 1, v___x_2063_);
lean_ctor_set(v___x_2067_, 2, v___x_2065_);
lean_ctor_set(v___x_2067_, 3, v___x_2066_);
v___x_2068_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2069_ = l_Lean_Syntax_node1(v___x_2061_, v___x_2068_, v_a_2052_);
v___x_2070_ = l_Lean_Syntax_node2(v___x_2061_, v___x_2062_, v___x_2067_, v___x_2069_);
if (v_isShared_2056_ == 0)
{
lean_ctor_set(v___x_2055_, 0, v___x_2070_);
v___x_2072_ = v___x_2055_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v___x_2070_);
lean_ctor_set(v_reuseFailAlloc_2073_, 1, v_a_2053_);
v___x_2072_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
return v___x_2072_;
}
}
}
case 15:
{
lean_object* v_presentation_2075_; lean_object* v___x_2076_; lean_object* v_a_2077_; lean_object* v_a_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2099_; 
v_presentation_2075_ = lean_ctor_get(v_x_1460_, 0);
lean_inc(v_presentation_2075_);
lean_dec_ref_known(v_x_1460_, 1);
v___x_2076_ = l___private_Std_Time_Notation_0__Std_Time_convertNumber(v_presentation_2075_, v_a_1461_, v_a_1462_);
v_a_2077_ = lean_ctor_get(v___x_2076_, 0);
v_a_2078_ = lean_ctor_get(v___x_2076_, 1);
v_isSharedCheck_2099_ = !lean_is_exclusive(v___x_2076_);
if (v_isSharedCheck_2099_ == 0)
{
v___x_2080_ = v___x_2076_;
v_isShared_2081_ = v_isSharedCheck_2099_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_a_2078_);
lean_inc(v_a_2077_);
lean_dec(v___x_2076_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2099_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
lean_object* v_quotContext_2082_; lean_object* v_currMacroScope_2083_; lean_object* v_ref_2084_; uint8_t v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2097_; 
v_quotContext_2082_ = lean_ctor_get(v_a_1461_, 1);
v_currMacroScope_2083_ = lean_ctor_get(v_a_1461_, 2);
v_ref_2084_ = lean_ctor_get(v_a_1461_, 5);
v___x_2085_ = 0;
v___x_2086_ = l_Lean_SourceInfo_fromRef(v_ref_2084_, v___x_2085_);
v___x_2087_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2088_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__157, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__157_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__157);
v___x_2089_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__159));
lean_inc(v_currMacroScope_2083_);
lean_inc(v_quotContext_2082_);
v___x_2090_ = l_Lean_addMacroScope(v_quotContext_2082_, v___x_2089_, v_currMacroScope_2083_);
v___x_2091_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__163));
lean_inc_n(v___x_2086_, 2);
v___x_2092_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2092_, 0, v___x_2086_);
lean_ctor_set(v___x_2092_, 1, v___x_2088_);
lean_ctor_set(v___x_2092_, 2, v___x_2090_);
lean_ctor_set(v___x_2092_, 3, v___x_2091_);
v___x_2093_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2094_ = l_Lean_Syntax_node1(v___x_2086_, v___x_2093_, v_a_2077_);
v___x_2095_ = l_Lean_Syntax_node2(v___x_2086_, v___x_2087_, v___x_2092_, v___x_2094_);
if (v_isShared_2081_ == 0)
{
lean_ctor_set(v___x_2080_, 0, v___x_2095_);
v___x_2097_ = v___x_2080_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v___x_2095_);
lean_ctor_set(v_reuseFailAlloc_2098_, 1, v_a_2078_);
v___x_2097_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
return v___x_2097_;
}
}
}
case 16:
{
lean_object* v_presentation_2100_; lean_object* v___x_2101_; lean_object* v_a_2102_; lean_object* v_a_2103_; lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2124_; 
v_presentation_2100_ = lean_ctor_get(v_x_1460_, 0);
lean_inc(v_presentation_2100_);
lean_dec_ref_known(v_x_1460_, 1);
v___x_2101_ = l___private_Std_Time_Notation_0__Std_Time_convertNumber(v_presentation_2100_, v_a_1461_, v_a_1462_);
v_a_2102_ = lean_ctor_get(v___x_2101_, 0);
v_a_2103_ = lean_ctor_get(v___x_2101_, 1);
v_isSharedCheck_2124_ = !lean_is_exclusive(v___x_2101_);
if (v_isSharedCheck_2124_ == 0)
{
v___x_2105_ = v___x_2101_;
v_isShared_2106_ = v_isSharedCheck_2124_;
goto v_resetjp_2104_;
}
else
{
lean_inc(v_a_2103_);
lean_inc(v_a_2102_);
lean_dec(v___x_2101_);
v___x_2105_ = lean_box(0);
v_isShared_2106_ = v_isSharedCheck_2124_;
goto v_resetjp_2104_;
}
v_resetjp_2104_:
{
lean_object* v_quotContext_2107_; lean_object* v_currMacroScope_2108_; lean_object* v_ref_2109_; uint8_t v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2122_; 
v_quotContext_2107_ = lean_ctor_get(v_a_1461_, 1);
v_currMacroScope_2108_ = lean_ctor_get(v_a_1461_, 2);
v_ref_2109_ = lean_ctor_get(v_a_1461_, 5);
v___x_2110_ = 0;
v___x_2111_ = l_Lean_SourceInfo_fromRef(v_ref_2109_, v___x_2110_);
v___x_2112_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2113_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__165, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__165_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__165);
v___x_2114_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__167));
lean_inc(v_currMacroScope_2108_);
lean_inc(v_quotContext_2107_);
v___x_2115_ = l_Lean_addMacroScope(v_quotContext_2107_, v___x_2114_, v_currMacroScope_2108_);
v___x_2116_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__171));
lean_inc_n(v___x_2111_, 2);
v___x_2117_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2117_, 0, v___x_2111_);
lean_ctor_set(v___x_2117_, 1, v___x_2113_);
lean_ctor_set(v___x_2117_, 2, v___x_2115_);
lean_ctor_set(v___x_2117_, 3, v___x_2116_);
v___x_2118_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2119_ = l_Lean_Syntax_node1(v___x_2111_, v___x_2118_, v_a_2102_);
v___x_2120_ = l_Lean_Syntax_node2(v___x_2111_, v___x_2112_, v___x_2117_, v___x_2119_);
if (v_isShared_2106_ == 0)
{
lean_ctor_set(v___x_2105_, 0, v___x_2120_);
v___x_2122_ = v___x_2105_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v___x_2120_);
lean_ctor_set(v_reuseFailAlloc_2123_, 1, v_a_2103_);
v___x_2122_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
return v___x_2122_;
}
}
}
case 17:
{
lean_object* v_presentation_2125_; lean_object* v___x_2126_; lean_object* v_a_2127_; lean_object* v_a_2128_; lean_object* v___x_2130_; uint8_t v_isShared_2131_; uint8_t v_isSharedCheck_2149_; 
v_presentation_2125_ = lean_ctor_get(v_x_1460_, 0);
lean_inc(v_presentation_2125_);
lean_dec_ref_known(v_x_1460_, 1);
v___x_2126_ = l___private_Std_Time_Notation_0__Std_Time_convertNumber(v_presentation_2125_, v_a_1461_, v_a_1462_);
v_a_2127_ = lean_ctor_get(v___x_2126_, 0);
v_a_2128_ = lean_ctor_get(v___x_2126_, 1);
v_isSharedCheck_2149_ = !lean_is_exclusive(v___x_2126_);
if (v_isSharedCheck_2149_ == 0)
{
v___x_2130_ = v___x_2126_;
v_isShared_2131_ = v_isSharedCheck_2149_;
goto v_resetjp_2129_;
}
else
{
lean_inc(v_a_2128_);
lean_inc(v_a_2127_);
lean_dec(v___x_2126_);
v___x_2130_ = lean_box(0);
v_isShared_2131_ = v_isSharedCheck_2149_;
goto v_resetjp_2129_;
}
v_resetjp_2129_:
{
lean_object* v_quotContext_2132_; lean_object* v_currMacroScope_2133_; lean_object* v_ref_2134_; uint8_t v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2147_; 
v_quotContext_2132_ = lean_ctor_get(v_a_1461_, 1);
v_currMacroScope_2133_ = lean_ctor_get(v_a_1461_, 2);
v_ref_2134_ = lean_ctor_get(v_a_1461_, 5);
v___x_2135_ = 0;
v___x_2136_ = l_Lean_SourceInfo_fromRef(v_ref_2134_, v___x_2135_);
v___x_2137_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2138_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__173, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__173_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__173);
v___x_2139_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__175));
lean_inc(v_currMacroScope_2133_);
lean_inc(v_quotContext_2132_);
v___x_2140_ = l_Lean_addMacroScope(v_quotContext_2132_, v___x_2139_, v_currMacroScope_2133_);
v___x_2141_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__179));
lean_inc_n(v___x_2136_, 2);
v___x_2142_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2142_, 0, v___x_2136_);
lean_ctor_set(v___x_2142_, 1, v___x_2138_);
lean_ctor_set(v___x_2142_, 2, v___x_2140_);
lean_ctor_set(v___x_2142_, 3, v___x_2141_);
v___x_2143_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2144_ = l_Lean_Syntax_node1(v___x_2136_, v___x_2143_, v_a_2127_);
v___x_2145_ = l_Lean_Syntax_node2(v___x_2136_, v___x_2137_, v___x_2142_, v___x_2144_);
if (v_isShared_2131_ == 0)
{
lean_ctor_set(v___x_2130_, 0, v___x_2145_);
v___x_2147_ = v___x_2130_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v___x_2145_);
lean_ctor_set(v_reuseFailAlloc_2148_, 1, v_a_2128_);
v___x_2147_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
return v___x_2147_;
}
}
}
case 18:
{
lean_object* v_presentation_2150_; lean_object* v___x_2151_; lean_object* v_a_2152_; lean_object* v_a_2153_; lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2174_; 
v_presentation_2150_ = lean_ctor_get(v_x_1460_, 0);
lean_inc(v_presentation_2150_);
lean_dec_ref_known(v_x_1460_, 1);
v___x_2151_ = l___private_Std_Time_Notation_0__Std_Time_convertNumber(v_presentation_2150_, v_a_1461_, v_a_1462_);
v_a_2152_ = lean_ctor_get(v___x_2151_, 0);
v_a_2153_ = lean_ctor_get(v___x_2151_, 1);
v_isSharedCheck_2174_ = !lean_is_exclusive(v___x_2151_);
if (v_isSharedCheck_2174_ == 0)
{
v___x_2155_ = v___x_2151_;
v_isShared_2156_ = v_isSharedCheck_2174_;
goto v_resetjp_2154_;
}
else
{
lean_inc(v_a_2153_);
lean_inc(v_a_2152_);
lean_dec(v___x_2151_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2174_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
lean_object* v_quotContext_2157_; lean_object* v_currMacroScope_2158_; lean_object* v_ref_2159_; uint8_t v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2172_; 
v_quotContext_2157_ = lean_ctor_get(v_a_1461_, 1);
v_currMacroScope_2158_ = lean_ctor_get(v_a_1461_, 2);
v_ref_2159_ = lean_ctor_get(v_a_1461_, 5);
v___x_2160_ = 0;
v___x_2161_ = l_Lean_SourceInfo_fromRef(v_ref_2159_, v___x_2160_);
v___x_2162_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2163_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__181, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__181_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__181);
v___x_2164_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__183));
lean_inc(v_currMacroScope_2158_);
lean_inc(v_quotContext_2157_);
v___x_2165_ = l_Lean_addMacroScope(v_quotContext_2157_, v___x_2164_, v_currMacroScope_2158_);
v___x_2166_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__187));
lean_inc_n(v___x_2161_, 2);
v___x_2167_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2167_, 0, v___x_2161_);
lean_ctor_set(v___x_2167_, 1, v___x_2163_);
lean_ctor_set(v___x_2167_, 2, v___x_2165_);
lean_ctor_set(v___x_2167_, 3, v___x_2166_);
v___x_2168_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2169_ = l_Lean_Syntax_node1(v___x_2161_, v___x_2168_, v_a_2152_);
v___x_2170_ = l_Lean_Syntax_node2(v___x_2161_, v___x_2162_, v___x_2167_, v___x_2169_);
if (v_isShared_2156_ == 0)
{
lean_ctor_set(v___x_2155_, 0, v___x_2170_);
v___x_2172_ = v___x_2155_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v___x_2170_);
lean_ctor_set(v_reuseFailAlloc_2173_, 1, v_a_2153_);
v___x_2172_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
return v___x_2172_;
}
}
}
case 19:
{
lean_object* v_presentation_2175_; lean_object* v___x_2176_; lean_object* v_a_2177_; lean_object* v_a_2178_; lean_object* v___x_2180_; uint8_t v_isShared_2181_; uint8_t v_isSharedCheck_2199_; 
v_presentation_2175_ = lean_ctor_get(v_x_1460_, 0);
lean_inc(v_presentation_2175_);
lean_dec_ref_known(v_x_1460_, 1);
v___x_2176_ = l___private_Std_Time_Notation_0__Std_Time_convertNumber(v_presentation_2175_, v_a_1461_, v_a_1462_);
v_a_2177_ = lean_ctor_get(v___x_2176_, 0);
v_a_2178_ = lean_ctor_get(v___x_2176_, 1);
v_isSharedCheck_2199_ = !lean_is_exclusive(v___x_2176_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_2180_ = v___x_2176_;
v_isShared_2181_ = v_isSharedCheck_2199_;
goto v_resetjp_2179_;
}
else
{
lean_inc(v_a_2178_);
lean_inc(v_a_2177_);
lean_dec(v___x_2176_);
v___x_2180_ = lean_box(0);
v_isShared_2181_ = v_isSharedCheck_2199_;
goto v_resetjp_2179_;
}
v_resetjp_2179_:
{
lean_object* v_quotContext_2182_; lean_object* v_currMacroScope_2183_; lean_object* v_ref_2184_; uint8_t v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2197_; 
v_quotContext_2182_ = lean_ctor_get(v_a_1461_, 1);
v_currMacroScope_2183_ = lean_ctor_get(v_a_1461_, 2);
v_ref_2184_ = lean_ctor_get(v_a_1461_, 5);
v___x_2185_ = 0;
v___x_2186_ = l_Lean_SourceInfo_fromRef(v_ref_2184_, v___x_2185_);
v___x_2187_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2188_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__189, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__189_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__189);
v___x_2189_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__191));
lean_inc(v_currMacroScope_2183_);
lean_inc(v_quotContext_2182_);
v___x_2190_ = l_Lean_addMacroScope(v_quotContext_2182_, v___x_2189_, v_currMacroScope_2183_);
v___x_2191_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__195));
lean_inc_n(v___x_2186_, 2);
v___x_2192_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2192_, 0, v___x_2186_);
lean_ctor_set(v___x_2192_, 1, v___x_2188_);
lean_ctor_set(v___x_2192_, 2, v___x_2190_);
lean_ctor_set(v___x_2192_, 3, v___x_2191_);
v___x_2193_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2194_ = l_Lean_Syntax_node1(v___x_2186_, v___x_2193_, v_a_2177_);
v___x_2195_ = l_Lean_Syntax_node2(v___x_2186_, v___x_2187_, v___x_2192_, v___x_2194_);
if (v_isShared_2181_ == 0)
{
lean_ctor_set(v___x_2180_, 0, v___x_2195_);
v___x_2197_ = v___x_2180_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v___x_2195_);
lean_ctor_set(v_reuseFailAlloc_2198_, 1, v_a_2178_);
v___x_2197_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
return v___x_2197_;
}
}
}
case 20:
{
lean_object* v_presentation_2200_; lean_object* v___x_2201_; lean_object* v_a_2202_; lean_object* v_a_2203_; lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2224_; 
v_presentation_2200_ = lean_ctor_get(v_x_1460_, 0);
lean_inc(v_presentation_2200_);
lean_dec_ref_known(v_x_1460_, 1);
v___x_2201_ = l___private_Std_Time_Notation_0__Std_Time_convertFraction(v_presentation_2200_, v_a_1461_, v_a_1462_);
v_a_2202_ = lean_ctor_get(v___x_2201_, 0);
v_a_2203_ = lean_ctor_get(v___x_2201_, 1);
v_isSharedCheck_2224_ = !lean_is_exclusive(v___x_2201_);
if (v_isSharedCheck_2224_ == 0)
{
v___x_2205_ = v___x_2201_;
v_isShared_2206_ = v_isSharedCheck_2224_;
goto v_resetjp_2204_;
}
else
{
lean_inc(v_a_2203_);
lean_inc(v_a_2202_);
lean_dec(v___x_2201_);
v___x_2205_ = lean_box(0);
v_isShared_2206_ = v_isSharedCheck_2224_;
goto v_resetjp_2204_;
}
v_resetjp_2204_:
{
lean_object* v_quotContext_2207_; lean_object* v_currMacroScope_2208_; lean_object* v_ref_2209_; uint8_t v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2222_; 
v_quotContext_2207_ = lean_ctor_get(v_a_1461_, 1);
v_currMacroScope_2208_ = lean_ctor_get(v_a_1461_, 2);
v_ref_2209_ = lean_ctor_get(v_a_1461_, 5);
v___x_2210_ = 0;
v___x_2211_ = l_Lean_SourceInfo_fromRef(v_ref_2209_, v___x_2210_);
v___x_2212_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2213_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__197, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__197_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__197);
v___x_2214_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__199));
lean_inc(v_currMacroScope_2208_);
lean_inc(v_quotContext_2207_);
v___x_2215_ = l_Lean_addMacroScope(v_quotContext_2207_, v___x_2214_, v_currMacroScope_2208_);
v___x_2216_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__203));
lean_inc_n(v___x_2211_, 2);
v___x_2217_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2217_, 0, v___x_2211_);
lean_ctor_set(v___x_2217_, 1, v___x_2213_);
lean_ctor_set(v___x_2217_, 2, v___x_2215_);
lean_ctor_set(v___x_2217_, 3, v___x_2216_);
v___x_2218_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2219_ = l_Lean_Syntax_node1(v___x_2211_, v___x_2218_, v_a_2202_);
v___x_2220_ = l_Lean_Syntax_node2(v___x_2211_, v___x_2212_, v___x_2217_, v___x_2219_);
if (v_isShared_2206_ == 0)
{
lean_ctor_set(v___x_2205_, 0, v___x_2220_);
v___x_2222_ = v___x_2205_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v___x_2220_);
lean_ctor_set(v_reuseFailAlloc_2223_, 1, v_a_2203_);
v___x_2222_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
return v___x_2222_;
}
}
}
case 21:
{
lean_object* v_presentation_2225_; lean_object* v___x_2226_; lean_object* v_a_2227_; lean_object* v_a_2228_; lean_object* v___x_2230_; uint8_t v_isShared_2231_; uint8_t v_isSharedCheck_2249_; 
v_presentation_2225_ = lean_ctor_get(v_x_1460_, 0);
lean_inc(v_presentation_2225_);
lean_dec_ref_known(v_x_1460_, 1);
v___x_2226_ = l___private_Std_Time_Notation_0__Std_Time_convertNumber(v_presentation_2225_, v_a_1461_, v_a_1462_);
v_a_2227_ = lean_ctor_get(v___x_2226_, 0);
v_a_2228_ = lean_ctor_get(v___x_2226_, 1);
v_isSharedCheck_2249_ = !lean_is_exclusive(v___x_2226_);
if (v_isSharedCheck_2249_ == 0)
{
v___x_2230_ = v___x_2226_;
v_isShared_2231_ = v_isSharedCheck_2249_;
goto v_resetjp_2229_;
}
else
{
lean_inc(v_a_2228_);
lean_inc(v_a_2227_);
lean_dec(v___x_2226_);
v___x_2230_ = lean_box(0);
v_isShared_2231_ = v_isSharedCheck_2249_;
goto v_resetjp_2229_;
}
v_resetjp_2229_:
{
lean_object* v_quotContext_2232_; lean_object* v_currMacroScope_2233_; lean_object* v_ref_2234_; uint8_t v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2247_; 
v_quotContext_2232_ = lean_ctor_get(v_a_1461_, 1);
v_currMacroScope_2233_ = lean_ctor_get(v_a_1461_, 2);
v_ref_2234_ = lean_ctor_get(v_a_1461_, 5);
v___x_2235_ = 0;
v___x_2236_ = l_Lean_SourceInfo_fromRef(v_ref_2234_, v___x_2235_);
v___x_2237_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2238_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__205, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__205_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__205);
v___x_2239_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__207));
lean_inc(v_currMacroScope_2233_);
lean_inc(v_quotContext_2232_);
v___x_2240_ = l_Lean_addMacroScope(v_quotContext_2232_, v___x_2239_, v_currMacroScope_2233_);
v___x_2241_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__211));
lean_inc_n(v___x_2236_, 2);
v___x_2242_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2242_, 0, v___x_2236_);
lean_ctor_set(v___x_2242_, 1, v___x_2238_);
lean_ctor_set(v___x_2242_, 2, v___x_2240_);
lean_ctor_set(v___x_2242_, 3, v___x_2241_);
v___x_2243_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2244_ = l_Lean_Syntax_node1(v___x_2236_, v___x_2243_, v_a_2227_);
v___x_2245_ = l_Lean_Syntax_node2(v___x_2236_, v___x_2237_, v___x_2242_, v___x_2244_);
if (v_isShared_2231_ == 0)
{
lean_ctor_set(v___x_2230_, 0, v___x_2245_);
v___x_2247_ = v___x_2230_;
goto v_reusejp_2246_;
}
else
{
lean_object* v_reuseFailAlloc_2248_; 
v_reuseFailAlloc_2248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2248_, 0, v___x_2245_);
lean_ctor_set(v_reuseFailAlloc_2248_, 1, v_a_2228_);
v___x_2247_ = v_reuseFailAlloc_2248_;
goto v_reusejp_2246_;
}
v_reusejp_2246_:
{
return v___x_2247_;
}
}
}
case 22:
{
lean_object* v_presentation_2250_; lean_object* v___x_2251_; lean_object* v_a_2252_; lean_object* v_a_2253_; lean_object* v___x_2255_; uint8_t v_isShared_2256_; uint8_t v_isSharedCheck_2274_; 
v_presentation_2250_ = lean_ctor_get(v_x_1460_, 0);
lean_inc(v_presentation_2250_);
lean_dec_ref_known(v_x_1460_, 1);
v___x_2251_ = l___private_Std_Time_Notation_0__Std_Time_convertNumber(v_presentation_2250_, v_a_1461_, v_a_1462_);
v_a_2252_ = lean_ctor_get(v___x_2251_, 0);
v_a_2253_ = lean_ctor_get(v___x_2251_, 1);
v_isSharedCheck_2274_ = !lean_is_exclusive(v___x_2251_);
if (v_isSharedCheck_2274_ == 0)
{
v___x_2255_ = v___x_2251_;
v_isShared_2256_ = v_isSharedCheck_2274_;
goto v_resetjp_2254_;
}
else
{
lean_inc(v_a_2253_);
lean_inc(v_a_2252_);
lean_dec(v___x_2251_);
v___x_2255_ = lean_box(0);
v_isShared_2256_ = v_isSharedCheck_2274_;
goto v_resetjp_2254_;
}
v_resetjp_2254_:
{
lean_object* v_quotContext_2257_; lean_object* v_currMacroScope_2258_; lean_object* v_ref_2259_; uint8_t v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2272_; 
v_quotContext_2257_ = lean_ctor_get(v_a_1461_, 1);
v_currMacroScope_2258_ = lean_ctor_get(v_a_1461_, 2);
v_ref_2259_ = lean_ctor_get(v_a_1461_, 5);
v___x_2260_ = 0;
v___x_2261_ = l_Lean_SourceInfo_fromRef(v_ref_2259_, v___x_2260_);
v___x_2262_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2263_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__213, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__213_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__213);
v___x_2264_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__215));
lean_inc(v_currMacroScope_2258_);
lean_inc(v_quotContext_2257_);
v___x_2265_ = l_Lean_addMacroScope(v_quotContext_2257_, v___x_2264_, v_currMacroScope_2258_);
v___x_2266_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__219));
lean_inc_n(v___x_2261_, 2);
v___x_2267_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2267_, 0, v___x_2261_);
lean_ctor_set(v___x_2267_, 1, v___x_2263_);
lean_ctor_set(v___x_2267_, 2, v___x_2265_);
lean_ctor_set(v___x_2267_, 3, v___x_2266_);
v___x_2268_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2269_ = l_Lean_Syntax_node1(v___x_2261_, v___x_2268_, v_a_2252_);
v___x_2270_ = l_Lean_Syntax_node2(v___x_2261_, v___x_2262_, v___x_2267_, v___x_2269_);
if (v_isShared_2256_ == 0)
{
lean_ctor_set(v___x_2255_, 0, v___x_2270_);
v___x_2272_ = v___x_2255_;
goto v_reusejp_2271_;
}
else
{
lean_object* v_reuseFailAlloc_2273_; 
v_reuseFailAlloc_2273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2273_, 0, v___x_2270_);
lean_ctor_set(v_reuseFailAlloc_2273_, 1, v_a_2253_);
v___x_2272_ = v_reuseFailAlloc_2273_;
goto v_reusejp_2271_;
}
v_reusejp_2271_:
{
return v___x_2272_;
}
}
}
case 23:
{
lean_object* v_presentation_2275_; lean_object* v___x_2276_; lean_object* v_a_2277_; lean_object* v_a_2278_; lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2299_; 
v_presentation_2275_ = lean_ctor_get(v_x_1460_, 0);
lean_inc(v_presentation_2275_);
lean_dec_ref_known(v_x_1460_, 1);
v___x_2276_ = l___private_Std_Time_Notation_0__Std_Time_convertNumber(v_presentation_2275_, v_a_1461_, v_a_1462_);
v_a_2277_ = lean_ctor_get(v___x_2276_, 0);
v_a_2278_ = lean_ctor_get(v___x_2276_, 1);
v_isSharedCheck_2299_ = !lean_is_exclusive(v___x_2276_);
if (v_isSharedCheck_2299_ == 0)
{
v___x_2280_ = v___x_2276_;
v_isShared_2281_ = v_isSharedCheck_2299_;
goto v_resetjp_2279_;
}
else
{
lean_inc(v_a_2278_);
lean_inc(v_a_2277_);
lean_dec(v___x_2276_);
v___x_2280_ = lean_box(0);
v_isShared_2281_ = v_isSharedCheck_2299_;
goto v_resetjp_2279_;
}
v_resetjp_2279_:
{
lean_object* v_quotContext_2282_; lean_object* v_currMacroScope_2283_; lean_object* v_ref_2284_; uint8_t v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2297_; 
v_quotContext_2282_ = lean_ctor_get(v_a_1461_, 1);
v_currMacroScope_2283_ = lean_ctor_get(v_a_1461_, 2);
v_ref_2284_ = lean_ctor_get(v_a_1461_, 5);
v___x_2285_ = 0;
v___x_2286_ = l_Lean_SourceInfo_fromRef(v_ref_2284_, v___x_2285_);
v___x_2287_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2288_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__221, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__221_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__221);
v___x_2289_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__223));
lean_inc(v_currMacroScope_2283_);
lean_inc(v_quotContext_2282_);
v___x_2290_ = l_Lean_addMacroScope(v_quotContext_2282_, v___x_2289_, v_currMacroScope_2283_);
v___x_2291_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__227));
lean_inc_n(v___x_2286_, 2);
v___x_2292_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2292_, 0, v___x_2286_);
lean_ctor_set(v___x_2292_, 1, v___x_2288_);
lean_ctor_set(v___x_2292_, 2, v___x_2290_);
lean_ctor_set(v___x_2292_, 3, v___x_2291_);
v___x_2293_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2294_ = l_Lean_Syntax_node1(v___x_2286_, v___x_2293_, v_a_2277_);
v___x_2295_ = l_Lean_Syntax_node2(v___x_2286_, v___x_2287_, v___x_2292_, v___x_2294_);
if (v_isShared_2281_ == 0)
{
lean_ctor_set(v___x_2280_, 0, v___x_2295_);
v___x_2297_ = v___x_2280_;
goto v_reusejp_2296_;
}
else
{
lean_object* v_reuseFailAlloc_2298_; 
v_reuseFailAlloc_2298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2298_, 0, v___x_2295_);
lean_ctor_set(v_reuseFailAlloc_2298_, 1, v_a_2278_);
v___x_2297_ = v_reuseFailAlloc_2298_;
goto v_reusejp_2296_;
}
v_reusejp_2296_:
{
return v___x_2297_;
}
}
}
case 24:
{
lean_object* v_quotContext_2300_; lean_object* v_currMacroScope_2301_; lean_object* v_ref_2302_; uint8_t v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; 
v_quotContext_2300_ = lean_ctor_get(v_a_1461_, 1);
v_currMacroScope_2301_ = lean_ctor_get(v_a_1461_, 2);
v_ref_2302_ = lean_ctor_get(v_a_1461_, 5);
v___x_2303_ = 0;
v___x_2304_ = l_Lean_SourceInfo_fromRef(v_ref_2302_, v___x_2303_);
v___x_2305_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__229, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__229_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__229);
v___x_2306_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__231));
lean_inc(v_currMacroScope_2301_);
lean_inc(v_quotContext_2300_);
v___x_2307_ = l_Lean_addMacroScope(v_quotContext_2300_, v___x_2306_, v_currMacroScope_2301_);
v___x_2308_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__235));
v___x_2309_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2309_, 0, v___x_2304_);
lean_ctor_set(v___x_2309_, 1, v___x_2305_);
lean_ctor_set(v___x_2309_, 2, v___x_2307_);
lean_ctor_set(v___x_2309_, 3, v___x_2308_);
v___x_2310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2310_, 0, v___x_2309_);
lean_ctor_set(v___x_2310_, 1, v_a_1462_);
return v___x_2310_;
}
case 25:
{
uint8_t v_presentation_2311_; lean_object* v___x_2312_; lean_object* v_a_2313_; lean_object* v_a_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2335_; 
v_presentation_2311_ = lean_ctor_get_uint8(v_x_1460_, 0);
lean_dec_ref_known(v_x_1460_, 0);
v___x_2312_ = l___private_Std_Time_Notation_0__Std_Time_convertZoneName(v_presentation_2311_, v_a_1461_, v_a_1462_);
v_a_2313_ = lean_ctor_get(v___x_2312_, 0);
v_a_2314_ = lean_ctor_get(v___x_2312_, 1);
v_isSharedCheck_2335_ = !lean_is_exclusive(v___x_2312_);
if (v_isSharedCheck_2335_ == 0)
{
v___x_2316_ = v___x_2312_;
v_isShared_2317_ = v_isSharedCheck_2335_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_a_2314_);
lean_inc(v_a_2313_);
lean_dec(v___x_2312_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2335_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
lean_object* v_quotContext_2318_; lean_object* v_currMacroScope_2319_; lean_object* v_ref_2320_; uint8_t v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2333_; 
v_quotContext_2318_ = lean_ctor_get(v_a_1461_, 1);
v_currMacroScope_2319_ = lean_ctor_get(v_a_1461_, 2);
v_ref_2320_ = lean_ctor_get(v_a_1461_, 5);
v___x_2321_ = 0;
v___x_2322_ = l_Lean_SourceInfo_fromRef(v_ref_2320_, v___x_2321_);
v___x_2323_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2324_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__237, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__237_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__237);
v___x_2325_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__239));
lean_inc(v_currMacroScope_2319_);
lean_inc(v_quotContext_2318_);
v___x_2326_ = l_Lean_addMacroScope(v_quotContext_2318_, v___x_2325_, v_currMacroScope_2319_);
v___x_2327_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__243));
lean_inc_n(v___x_2322_, 2);
v___x_2328_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2328_, 0, v___x_2322_);
lean_ctor_set(v___x_2328_, 1, v___x_2324_);
lean_ctor_set(v___x_2328_, 2, v___x_2326_);
lean_ctor_set(v___x_2328_, 3, v___x_2327_);
v___x_2329_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2330_ = l_Lean_Syntax_node1(v___x_2322_, v___x_2329_, v_a_2313_);
v___x_2331_ = l_Lean_Syntax_node2(v___x_2322_, v___x_2323_, v___x_2328_, v___x_2330_);
if (v_isShared_2317_ == 0)
{
lean_ctor_set(v___x_2316_, 0, v___x_2331_);
v___x_2333_ = v___x_2316_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v___x_2331_);
lean_ctor_set(v_reuseFailAlloc_2334_, 1, v_a_2314_);
v___x_2333_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
return v___x_2333_;
}
}
}
case 26:
{
uint8_t v_presentation_2336_; lean_object* v___x_2337_; lean_object* v_a_2338_; lean_object* v_a_2339_; lean_object* v___x_2341_; uint8_t v_isShared_2342_; uint8_t v_isSharedCheck_2360_; 
v_presentation_2336_ = lean_ctor_get_uint8(v_x_1460_, 0);
lean_dec_ref_known(v_x_1460_, 0);
v___x_2337_ = l___private_Std_Time_Notation_0__Std_Time_convertOffsetO(v_presentation_2336_, v_a_1461_, v_a_1462_);
v_a_2338_ = lean_ctor_get(v___x_2337_, 0);
v_a_2339_ = lean_ctor_get(v___x_2337_, 1);
v_isSharedCheck_2360_ = !lean_is_exclusive(v___x_2337_);
if (v_isSharedCheck_2360_ == 0)
{
v___x_2341_ = v___x_2337_;
v_isShared_2342_ = v_isSharedCheck_2360_;
goto v_resetjp_2340_;
}
else
{
lean_inc(v_a_2339_);
lean_inc(v_a_2338_);
lean_dec(v___x_2337_);
v___x_2341_ = lean_box(0);
v_isShared_2342_ = v_isSharedCheck_2360_;
goto v_resetjp_2340_;
}
v_resetjp_2340_:
{
lean_object* v_quotContext_2343_; lean_object* v_currMacroScope_2344_; lean_object* v_ref_2345_; uint8_t v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2358_; 
v_quotContext_2343_ = lean_ctor_get(v_a_1461_, 1);
v_currMacroScope_2344_ = lean_ctor_get(v_a_1461_, 2);
v_ref_2345_ = lean_ctor_get(v_a_1461_, 5);
v___x_2346_ = 0;
v___x_2347_ = l_Lean_SourceInfo_fromRef(v_ref_2345_, v___x_2346_);
v___x_2348_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2349_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__245, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__245_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__245);
v___x_2350_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__247));
lean_inc(v_currMacroScope_2344_);
lean_inc(v_quotContext_2343_);
v___x_2351_ = l_Lean_addMacroScope(v_quotContext_2343_, v___x_2350_, v_currMacroScope_2344_);
v___x_2352_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__251));
lean_inc_n(v___x_2347_, 2);
v___x_2353_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2353_, 0, v___x_2347_);
lean_ctor_set(v___x_2353_, 1, v___x_2349_);
lean_ctor_set(v___x_2353_, 2, v___x_2351_);
lean_ctor_set(v___x_2353_, 3, v___x_2352_);
v___x_2354_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2355_ = l_Lean_Syntax_node1(v___x_2347_, v___x_2354_, v_a_2338_);
v___x_2356_ = l_Lean_Syntax_node2(v___x_2347_, v___x_2348_, v___x_2353_, v___x_2355_);
if (v_isShared_2342_ == 0)
{
lean_ctor_set(v___x_2341_, 0, v___x_2356_);
v___x_2358_ = v___x_2341_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v___x_2356_);
lean_ctor_set(v_reuseFailAlloc_2359_, 1, v_a_2339_);
v___x_2358_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
return v___x_2358_;
}
}
}
case 27:
{
uint8_t v_presentation_2361_; lean_object* v___x_2362_; lean_object* v_a_2363_; lean_object* v_a_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2385_; 
v_presentation_2361_ = lean_ctor_get_uint8(v_x_1460_, 0);
lean_dec_ref_known(v_x_1460_, 0);
v___x_2362_ = l___private_Std_Time_Notation_0__Std_Time_convertOffsetX(v_presentation_2361_, v_a_1461_, v_a_1462_);
v_a_2363_ = lean_ctor_get(v___x_2362_, 0);
v_a_2364_ = lean_ctor_get(v___x_2362_, 1);
v_isSharedCheck_2385_ = !lean_is_exclusive(v___x_2362_);
if (v_isSharedCheck_2385_ == 0)
{
v___x_2366_ = v___x_2362_;
v_isShared_2367_ = v_isSharedCheck_2385_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_a_2364_);
lean_inc(v_a_2363_);
lean_dec(v___x_2362_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2385_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
lean_object* v_quotContext_2368_; lean_object* v_currMacroScope_2369_; lean_object* v_ref_2370_; uint8_t v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2383_; 
v_quotContext_2368_ = lean_ctor_get(v_a_1461_, 1);
v_currMacroScope_2369_ = lean_ctor_get(v_a_1461_, 2);
v_ref_2370_ = lean_ctor_get(v_a_1461_, 5);
v___x_2371_ = 0;
v___x_2372_ = l_Lean_SourceInfo_fromRef(v_ref_2370_, v___x_2371_);
v___x_2373_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2374_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__253, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__253_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__253);
v___x_2375_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__255));
lean_inc(v_currMacroScope_2369_);
lean_inc(v_quotContext_2368_);
v___x_2376_ = l_Lean_addMacroScope(v_quotContext_2368_, v___x_2375_, v_currMacroScope_2369_);
v___x_2377_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__259));
lean_inc_n(v___x_2372_, 2);
v___x_2378_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2378_, 0, v___x_2372_);
lean_ctor_set(v___x_2378_, 1, v___x_2374_);
lean_ctor_set(v___x_2378_, 2, v___x_2376_);
lean_ctor_set(v___x_2378_, 3, v___x_2377_);
v___x_2379_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2380_ = l_Lean_Syntax_node1(v___x_2372_, v___x_2379_, v_a_2363_);
v___x_2381_ = l_Lean_Syntax_node2(v___x_2372_, v___x_2373_, v___x_2378_, v___x_2380_);
if (v_isShared_2367_ == 0)
{
lean_ctor_set(v___x_2366_, 0, v___x_2381_);
v___x_2383_ = v___x_2366_;
goto v_reusejp_2382_;
}
else
{
lean_object* v_reuseFailAlloc_2384_; 
v_reuseFailAlloc_2384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2384_, 0, v___x_2381_);
lean_ctor_set(v_reuseFailAlloc_2384_, 1, v_a_2364_);
v___x_2383_ = v_reuseFailAlloc_2384_;
goto v_reusejp_2382_;
}
v_reusejp_2382_:
{
return v___x_2383_;
}
}
}
case 28:
{
uint8_t v_presentation_2386_; lean_object* v___x_2387_; lean_object* v_a_2388_; lean_object* v_a_2389_; lean_object* v___x_2391_; uint8_t v_isShared_2392_; uint8_t v_isSharedCheck_2410_; 
v_presentation_2386_ = lean_ctor_get_uint8(v_x_1460_, 0);
lean_dec_ref_known(v_x_1460_, 0);
v___x_2387_ = l___private_Std_Time_Notation_0__Std_Time_convertOffsetX(v_presentation_2386_, v_a_1461_, v_a_1462_);
v_a_2388_ = lean_ctor_get(v___x_2387_, 0);
v_a_2389_ = lean_ctor_get(v___x_2387_, 1);
v_isSharedCheck_2410_ = !lean_is_exclusive(v___x_2387_);
if (v_isSharedCheck_2410_ == 0)
{
v___x_2391_ = v___x_2387_;
v_isShared_2392_ = v_isSharedCheck_2410_;
goto v_resetjp_2390_;
}
else
{
lean_inc(v_a_2389_);
lean_inc(v_a_2388_);
lean_dec(v___x_2387_);
v___x_2391_ = lean_box(0);
v_isShared_2392_ = v_isSharedCheck_2410_;
goto v_resetjp_2390_;
}
v_resetjp_2390_:
{
lean_object* v_quotContext_2393_; lean_object* v_currMacroScope_2394_; lean_object* v_ref_2395_; uint8_t v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2408_; 
v_quotContext_2393_ = lean_ctor_get(v_a_1461_, 1);
v_currMacroScope_2394_ = lean_ctor_get(v_a_1461_, 2);
v_ref_2395_ = lean_ctor_get(v_a_1461_, 5);
v___x_2396_ = 0;
v___x_2397_ = l_Lean_SourceInfo_fromRef(v_ref_2395_, v___x_2396_);
v___x_2398_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2399_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__261, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__261_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__261);
v___x_2400_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__263));
lean_inc(v_currMacroScope_2394_);
lean_inc(v_quotContext_2393_);
v___x_2401_ = l_Lean_addMacroScope(v_quotContext_2393_, v___x_2400_, v_currMacroScope_2394_);
v___x_2402_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__267));
lean_inc_n(v___x_2397_, 2);
v___x_2403_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2403_, 0, v___x_2397_);
lean_ctor_set(v___x_2403_, 1, v___x_2399_);
lean_ctor_set(v___x_2403_, 2, v___x_2401_);
lean_ctor_set(v___x_2403_, 3, v___x_2402_);
v___x_2404_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2405_ = l_Lean_Syntax_node1(v___x_2397_, v___x_2404_, v_a_2388_);
v___x_2406_ = l_Lean_Syntax_node2(v___x_2397_, v___x_2398_, v___x_2403_, v___x_2405_);
if (v_isShared_2392_ == 0)
{
lean_ctor_set(v___x_2391_, 0, v___x_2406_);
v___x_2408_ = v___x_2391_;
goto v_reusejp_2407_;
}
else
{
lean_object* v_reuseFailAlloc_2409_; 
v_reuseFailAlloc_2409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2409_, 0, v___x_2406_);
lean_ctor_set(v_reuseFailAlloc_2409_, 1, v_a_2389_);
v___x_2408_ = v_reuseFailAlloc_2409_;
goto v_reusejp_2407_;
}
v_reusejp_2407_:
{
return v___x_2408_;
}
}
}
default: 
{
uint8_t v_presentation_2411_; lean_object* v___x_2412_; lean_object* v_a_2413_; lean_object* v_a_2414_; lean_object* v___x_2416_; uint8_t v_isShared_2417_; uint8_t v_isSharedCheck_2435_; 
v_presentation_2411_ = lean_ctor_get_uint8(v_x_1460_, 0);
lean_dec_ref_known(v_x_1460_, 0);
v___x_2412_ = l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ(v_presentation_2411_, v_a_1461_, v_a_1462_);
v_a_2413_ = lean_ctor_get(v___x_2412_, 0);
v_a_2414_ = lean_ctor_get(v___x_2412_, 1);
v_isSharedCheck_2435_ = !lean_is_exclusive(v___x_2412_);
if (v_isSharedCheck_2435_ == 0)
{
v___x_2416_ = v___x_2412_;
v_isShared_2417_ = v_isSharedCheck_2435_;
goto v_resetjp_2415_;
}
else
{
lean_inc(v_a_2414_);
lean_inc(v_a_2413_);
lean_dec(v___x_2412_);
v___x_2416_ = lean_box(0);
v_isShared_2417_ = v_isSharedCheck_2435_;
goto v_resetjp_2415_;
}
v_resetjp_2415_:
{
lean_object* v_quotContext_2418_; lean_object* v_currMacroScope_2419_; lean_object* v_ref_2420_; uint8_t v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2433_; 
v_quotContext_2418_ = lean_ctor_get(v_a_1461_, 1);
v_currMacroScope_2419_ = lean_ctor_get(v_a_1461_, 2);
v_ref_2420_ = lean_ctor_get(v_a_1461_, 5);
v___x_2421_ = 0;
v___x_2422_ = l_Lean_SourceInfo_fromRef(v_ref_2420_, v___x_2421_);
v___x_2423_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2424_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__269, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__269_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__269);
v___x_2425_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__271));
lean_inc(v_currMacroScope_2419_);
lean_inc(v_quotContext_2418_);
v___x_2426_ = l_Lean_addMacroScope(v_quotContext_2418_, v___x_2425_, v_currMacroScope_2419_);
v___x_2427_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__275));
lean_inc_n(v___x_2422_, 2);
v___x_2428_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2428_, 0, v___x_2422_);
lean_ctor_set(v___x_2428_, 1, v___x_2424_);
lean_ctor_set(v___x_2428_, 2, v___x_2426_);
lean_ctor_set(v___x_2428_, 3, v___x_2427_);
v___x_2429_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2430_ = l_Lean_Syntax_node1(v___x_2422_, v___x_2429_, v_a_2413_);
v___x_2431_ = l_Lean_Syntax_node2(v___x_2422_, v___x_2423_, v___x_2428_, v___x_2430_);
if (v_isShared_2417_ == 0)
{
lean_ctor_set(v___x_2416_, 0, v___x_2431_);
v___x_2433_ = v___x_2416_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v___x_2431_);
lean_ctor_set(v_reuseFailAlloc_2434_, 1, v_a_2414_);
v___x_2433_ = v_reuseFailAlloc_2434_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
return v___x_2433_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___boxed(lean_object* v_x_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_){
_start:
{
lean_object* v_res_2439_; 
v_res_2439_ = l___private_Std_Time_Notation_0__Std_Time_convertModifier(v_x_2436_, v_a_2437_, v_a_2438_);
lean_dec_ref(v_a_2437_);
return v_res_2439_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertFormatPart___closed__1(void){
_start:
{
lean_object* v___x_2441_; lean_object* v___x_2442_; 
v___x_2441_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertFormatPart___closed__0));
v___x_2442_ = l_String_toRawSubstring_x27(v___x_2441_);
return v___x_2442_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertFormatPart___closed__4(void){
_start:
{
lean_object* v___x_2446_; lean_object* v___x_2447_; 
v___x_2446_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertFormatPart___closed__3));
v___x_2447_ = l_String_toRawSubstring_x27(v___x_2446_);
return v___x_2447_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertFormatPart(lean_object* v_x_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_){
_start:
{
if (lean_obj_tag(v_x_2450_) == 0)
{
lean_object* v_val_2453_; lean_object* v_quotContext_2454_; lean_object* v_currMacroScope_2455_; lean_object* v_ref_2456_; uint8_t v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; 
v_val_2453_ = lean_ctor_get(v_x_2450_, 0);
lean_inc_ref(v_val_2453_);
lean_dec_ref_known(v_x_2450_, 1);
v_quotContext_2454_ = lean_ctor_get(v_a_2451_, 1);
v_currMacroScope_2455_ = lean_ctor_get(v_a_2451_, 2);
v_ref_2456_ = lean_ctor_get(v_a_2451_, 5);
v___x_2457_ = 0;
v___x_2458_ = l_Lean_SourceInfo_fromRef(v_ref_2456_, v___x_2457_);
v___x_2459_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2460_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__75));
v___x_2461_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__76));
lean_inc_n(v___x_2458_, 4);
v___x_2462_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2462_, 0, v___x_2458_);
lean_ctor_set(v___x_2462_, 1, v___x_2461_);
v___x_2463_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertFormatPart___closed__1, &l___private_Std_Time_Notation_0__Std_Time_convertFormatPart___closed__1_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertFormatPart___closed__1);
v___x_2464_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertFormatPart___closed__2));
lean_inc(v_currMacroScope_2455_);
lean_inc(v_quotContext_2454_);
v___x_2465_ = l_Lean_addMacroScope(v_quotContext_2454_, v___x_2464_, v_currMacroScope_2455_);
v___x_2466_ = lean_box(0);
v___x_2467_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2467_, 0, v___x_2458_);
lean_ctor_set(v___x_2467_, 1, v___x_2463_);
lean_ctor_set(v___x_2467_, 2, v___x_2465_);
lean_ctor_set(v___x_2467_, 3, v___x_2466_);
v___x_2468_ = l_Lean_Syntax_node2(v___x_2458_, v___x_2460_, v___x_2462_, v___x_2467_);
v___x_2469_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2470_ = lean_box(2);
v___x_2471_ = l_Lean_Syntax_mkStrLit(v_val_2453_, v___x_2470_);
v___x_2472_ = l_Lean_Syntax_node1(v___x_2458_, v___x_2469_, v___x_2471_);
v___x_2473_ = l_Lean_Syntax_node2(v___x_2458_, v___x_2459_, v___x_2468_, v___x_2472_);
v___x_2474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2474_, 0, v___x_2473_);
lean_ctor_set(v___x_2474_, 1, v_a_2452_);
return v___x_2474_;
}
else
{
lean_object* v_modifier_2475_; lean_object* v___x_2476_; lean_object* v_a_2477_; lean_object* v_a_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2503_; 
v_modifier_2475_ = lean_ctor_get(v_x_2450_, 0);
lean_inc(v_modifier_2475_);
lean_dec_ref_known(v_x_2450_, 1);
v___x_2476_ = l___private_Std_Time_Notation_0__Std_Time_convertModifier(v_modifier_2475_, v_a_2451_, v_a_2452_);
v_a_2477_ = lean_ctor_get(v___x_2476_, 0);
v_a_2478_ = lean_ctor_get(v___x_2476_, 1);
v_isSharedCheck_2503_ = !lean_is_exclusive(v___x_2476_);
if (v_isSharedCheck_2503_ == 0)
{
v___x_2480_ = v___x_2476_;
v_isShared_2481_ = v_isSharedCheck_2503_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_a_2478_);
lean_inc(v_a_2477_);
lean_dec(v___x_2476_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2503_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
lean_object* v_quotContext_2482_; lean_object* v_currMacroScope_2483_; lean_object* v_ref_2484_; uint8_t v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2501_; 
v_quotContext_2482_ = lean_ctor_get(v_a_2451_, 1);
v_currMacroScope_2483_ = lean_ctor_get(v_a_2451_, 2);
v_ref_2484_ = lean_ctor_get(v_a_2451_, 5);
v___x_2485_ = 0;
v___x_2486_ = l_Lean_SourceInfo_fromRef(v_ref_2484_, v___x_2485_);
v___x_2487_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2488_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__75));
v___x_2489_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__76));
lean_inc_n(v___x_2486_, 4);
v___x_2490_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2490_, 0, v___x_2486_);
lean_ctor_set(v___x_2490_, 1, v___x_2489_);
v___x_2491_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertFormatPart___closed__4, &l___private_Std_Time_Notation_0__Std_Time_convertFormatPart___closed__4_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertFormatPart___closed__4);
v___x_2492_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertFormatPart___closed__5));
lean_inc(v_currMacroScope_2483_);
lean_inc(v_quotContext_2482_);
v___x_2493_ = l_Lean_addMacroScope(v_quotContext_2482_, v___x_2492_, v_currMacroScope_2483_);
v___x_2494_ = lean_box(0);
v___x_2495_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2495_, 0, v___x_2486_);
lean_ctor_set(v___x_2495_, 1, v___x_2491_);
lean_ctor_set(v___x_2495_, 2, v___x_2493_);
lean_ctor_set(v___x_2495_, 3, v___x_2494_);
v___x_2496_ = l_Lean_Syntax_node2(v___x_2486_, v___x_2488_, v___x_2490_, v___x_2495_);
v___x_2497_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2498_ = l_Lean_Syntax_node1(v___x_2486_, v___x_2497_, v_a_2477_);
v___x_2499_ = l_Lean_Syntax_node2(v___x_2486_, v___x_2487_, v___x_2496_, v___x_2498_);
if (v_isShared_2481_ == 0)
{
lean_ctor_set(v___x_2480_, 0, v___x_2499_);
v___x_2501_ = v___x_2480_;
goto v_reusejp_2500_;
}
else
{
lean_object* v_reuseFailAlloc_2502_; 
v_reuseFailAlloc_2502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2502_, 0, v___x_2499_);
lean_ctor_set(v_reuseFailAlloc_2502_, 1, v_a_2478_);
v___x_2501_ = v_reuseFailAlloc_2502_;
goto v_reusejp_2500_;
}
v_reusejp_2500_:
{
return v___x_2501_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertFormatPart___boxed(lean_object* v_x_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_){
_start:
{
lean_object* v_res_2507_; 
v_res_2507_ = l___private_Std_Time_Notation_0__Std_Time_convertFormatPart(v_x_2504_, v_a_2505_, v_a_2506_);
lean_dec_ref(v_a_2505_);
return v_res_2507_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxNat(lean_object* v_n_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_){
_start:
{
lean_object* v_ref_2514_; uint8_t v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; 
v_ref_2514_ = lean_ctor_get(v_a_2512_, 5);
v___x_2515_ = 0;
v___x_2516_ = l_Lean_SourceInfo_fromRef(v_ref_2514_, v___x_2515_);
v___x_2517_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxNat___closed__1));
v___x_2518_ = l_Nat_reprFast(v_n_2511_);
lean_inc(v___x_2516_);
v___x_2519_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2519_, 0, v___x_2516_);
lean_ctor_set(v___x_2519_, 1, v___x_2518_);
v___x_2520_ = l_Lean_Syntax_node1(v___x_2516_, v___x_2517_, v___x_2519_);
v___x_2521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2521_, 0, v___x_2520_);
lean_ctor_set(v___x_2521_, 1, v_a_2513_);
return v___x_2521_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxNat___boxed(lean_object* v_n_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_){
_start:
{
lean_object* v_res_2525_; 
v_res_2525_ = l___private_Std_Time_Notation_0__Std_Time_syntaxNat(v_n_2522_, v_a_2523_, v_a_2524_);
lean_dec_ref(v_a_2523_);
return v_res_2525_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxString(lean_object* v_n_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_){
_start:
{
lean_object* v_ref_2532_; uint8_t v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; 
v_ref_2532_ = lean_ctor_get(v_a_2530_, 5);
v___x_2533_ = 0;
v___x_2534_ = l_Lean_SourceInfo_fromRef(v_ref_2532_, v___x_2533_);
v___x_2535_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxString___closed__1));
lean_inc(v___x_2534_);
v___x_2536_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2536_, 0, v___x_2534_);
lean_ctor_set(v___x_2536_, 1, v_n_2529_);
v___x_2537_ = l_Lean_Syntax_node1(v___x_2534_, v___x_2535_, v___x_2536_);
v___x_2538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2538_, 0, v___x_2537_);
lean_ctor_set(v___x_2538_, 1, v_a_2531_);
return v___x_2538_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxString___boxed(lean_object* v_n_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_){
_start:
{
lean_object* v_res_2542_; 
v_res_2542_ = l___private_Std_Time_Notation_0__Std_Time_syntaxString(v_n_2539_, v_a_2540_, v_a_2541_);
lean_dec_ref(v_a_2540_);
return v_res_2542_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__0(void){
_start:
{
lean_object* v_natZero_2543_; lean_object* v_intZero_2544_; 
v_natZero_2543_ = lean_unsigned_to_nat(0u);
v_intZero_2544_ = lean_nat_to_int(v_natZero_2543_);
return v_intZero_2544_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__2(void){
_start:
{
lean_object* v___x_2546_; lean_object* v___x_2547_; 
v___x_2546_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__1));
v___x_2547_ = l_String_toRawSubstring_x27(v___x_2546_);
return v___x_2547_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__11(void){
_start:
{
lean_object* v___x_2565_; lean_object* v___x_2566_; 
v___x_2565_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__10));
v___x_2566_ = l_String_toRawSubstring_x27(v___x_2565_);
return v___x_2566_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxInt(lean_object* v_n_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_){
_start:
{
lean_object* v_intZero_2585_; uint8_t v_isNeg_2586_; 
v_intZero_2585_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__0, &l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__0_once, _init_l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__0);
v_isNeg_2586_ = lean_int_dec_lt(v_n_2582_, v_intZero_2585_);
if (v_isNeg_2586_ == 0)
{
lean_object* v_quotContext_2587_; lean_object* v_currMacroScope_2588_; lean_object* v_ref_2589_; lean_object* v_a_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; 
v_quotContext_2587_ = lean_ctor_get(v_a_2583_, 1);
v_currMacroScope_2588_ = lean_ctor_get(v_a_2583_, 2);
v_ref_2589_ = lean_ctor_get(v_a_2583_, 5);
v_a_2590_ = lean_nat_abs(v_n_2582_);
v___x_2591_ = l_Lean_SourceInfo_fromRef(v_ref_2589_, v_isNeg_2586_);
v___x_2592_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2593_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__2, &l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__2_once, _init_l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__2);
v___x_2594_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__5));
lean_inc(v_currMacroScope_2588_);
lean_inc(v_quotContext_2587_);
v___x_2595_ = l_Lean_addMacroScope(v_quotContext_2587_, v___x_2594_, v_currMacroScope_2588_);
v___x_2596_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__9));
lean_inc_n(v___x_2591_, 2);
v___x_2597_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2597_, 0, v___x_2591_);
lean_ctor_set(v___x_2597_, 1, v___x_2593_);
lean_ctor_set(v___x_2597_, 2, v___x_2595_);
lean_ctor_set(v___x_2597_, 3, v___x_2596_);
v___x_2598_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2599_ = l_Nat_reprFast(v_a_2590_);
v___x_2600_ = lean_box(2);
v___x_2601_ = l_Lean_Syntax_mkNumLit(v___x_2599_, v___x_2600_);
v___x_2602_ = l_Lean_Syntax_node1(v___x_2591_, v___x_2598_, v___x_2601_);
v___x_2603_ = l_Lean_Syntax_node2(v___x_2591_, v___x_2592_, v___x_2597_, v___x_2602_);
v___x_2604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2604_, 0, v___x_2603_);
lean_ctor_set(v___x_2604_, 1, v_a_2584_);
return v___x_2604_;
}
else
{
lean_object* v_quotContext_2605_; lean_object* v_currMacroScope_2606_; lean_object* v_ref_2607_; lean_object* v_abs_2608_; lean_object* v_one_2609_; lean_object* v_a_2610_; uint8_t v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; 
v_quotContext_2605_ = lean_ctor_get(v_a_2583_, 1);
v_currMacroScope_2606_ = lean_ctor_get(v_a_2583_, 2);
v_ref_2607_ = lean_ctor_get(v_a_2583_, 5);
v_abs_2608_ = lean_nat_abs(v_n_2582_);
v_one_2609_ = lean_unsigned_to_nat(1u);
v_a_2610_ = lean_nat_sub(v_abs_2608_, v_one_2609_);
lean_dec(v_abs_2608_);
v___x_2611_ = 0;
v___x_2612_ = l_Lean_SourceInfo_fromRef(v_ref_2607_, v___x_2611_);
v___x_2613_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2614_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__11, &l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__11_once, _init_l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__11);
v___x_2615_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__13));
lean_inc(v_currMacroScope_2606_);
lean_inc(v_quotContext_2605_);
v___x_2616_ = l_Lean_addMacroScope(v_quotContext_2605_, v___x_2615_, v_currMacroScope_2606_);
v___x_2617_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__17));
lean_inc_n(v___x_2612_, 2);
v___x_2618_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2618_, 0, v___x_2612_);
lean_ctor_set(v___x_2618_, 1, v___x_2614_);
lean_ctor_set(v___x_2618_, 2, v___x_2616_);
lean_ctor_set(v___x_2618_, 3, v___x_2617_);
v___x_2619_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2620_ = l_Nat_reprFast(v_a_2610_);
v___x_2621_ = lean_box(2);
v___x_2622_ = l_Lean_Syntax_mkNumLit(v___x_2620_, v___x_2621_);
v___x_2623_ = l_Lean_Syntax_node1(v___x_2612_, v___x_2619_, v___x_2622_);
v___x_2624_ = l_Lean_Syntax_node2(v___x_2612_, v___x_2613_, v___x_2618_, v___x_2623_);
v___x_2625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2625_, 0, v___x_2624_);
lean_ctor_set(v___x_2625_, 1, v_a_2584_);
return v___x_2625_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxInt___boxed(lean_object* v_n_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_){
_start:
{
lean_object* v_res_2629_; 
v_res_2629_ = l___private_Std_Time_Notation_0__Std_Time_syntaxInt(v_n_2626_, v_a_2627_, v_a_2628_);
lean_dec_ref(v_a_2627_);
lean_dec(v_n_2626_);
return v_res_2629_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__1(void){
_start:
{
lean_object* v___x_2631_; lean_object* v___x_2632_; 
v___x_2631_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__0));
v___x_2632_ = l_String_toRawSubstring_x27(v___x_2631_);
return v___x_2632_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__21(void){
_start:
{
lean_object* v___x_2682_; 
v___x_2682_ = l_Array_mkArray0(lean_box(0));
return v___x_2682_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxBounded(lean_object* v_n_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_){
_start:
{
lean_object* v___x_2686_; lean_object* v_a_2687_; lean_object* v_a_2688_; lean_object* v___x_2690_; uint8_t v_isShared_2691_; uint8_t v_isSharedCheck_2741_; 
v___x_2686_ = l___private_Std_Time_Notation_0__Std_Time_syntaxInt(v_n_2683_, v_a_2684_, v_a_2685_);
v_a_2687_ = lean_ctor_get(v___x_2686_, 0);
v_a_2688_ = lean_ctor_get(v___x_2686_, 1);
v_isSharedCheck_2741_ = !lean_is_exclusive(v___x_2686_);
if (v_isSharedCheck_2741_ == 0)
{
v___x_2690_ = v___x_2686_;
v_isShared_2691_ = v_isSharedCheck_2741_;
goto v_resetjp_2689_;
}
else
{
lean_inc(v_a_2688_);
lean_inc(v_a_2687_);
lean_dec(v___x_2686_);
v___x_2690_ = lean_box(0);
v_isShared_2691_ = v_isSharedCheck_2741_;
goto v_resetjp_2689_;
}
v_resetjp_2689_:
{
lean_object* v_quotContext_2692_; lean_object* v_currMacroScope_2693_; lean_object* v_ref_2694_; uint8_t v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2739_; 
v_quotContext_2692_ = lean_ctor_get(v_a_2684_, 1);
v_currMacroScope_2693_ = lean_ctor_get(v_a_2684_, 2);
v_ref_2694_ = lean_ctor_get(v_a_2684_, 5);
v___x_2695_ = 0;
v___x_2696_ = l_Lean_SourceInfo_fromRef(v_ref_2694_, v___x_2695_);
v___x_2697_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2698_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__1, &l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__1_once, _init_l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__1);
v___x_2699_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__6));
lean_inc_n(v_currMacroScope_2693_, 2);
lean_inc_n(v_quotContext_2692_, 2);
v___x_2700_ = l_Lean_addMacroScope(v_quotContext_2692_, v___x_2699_, v_currMacroScope_2693_);
v___x_2701_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__8));
lean_inc_n(v___x_2696_, 17);
v___x_2702_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2702_, 0, v___x_2696_);
lean_ctor_set(v___x_2702_, 1, v___x_2698_);
lean_ctor_set(v___x_2702_, 2, v___x_2700_);
lean_ctor_set(v___x_2702_, 3, v___x_2701_);
v___x_2703_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2704_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__50));
v___x_2705_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__52));
v___x_2706_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__53));
v___x_2707_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2707_, 0, v___x_2696_);
lean_ctor_set(v___x_2707_, 1, v___x_2706_);
v___x_2708_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__55));
v___x_2709_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__57, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__57_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__57);
v___x_2710_ = lean_box(0);
v___x_2711_ = l_Lean_addMacroScope(v_quotContext_2692_, v___x_2710_, v_currMacroScope_2693_);
v___x_2712_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__73));
v___x_2713_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2713_, 0, v___x_2696_);
lean_ctor_set(v___x_2713_, 1, v___x_2709_);
lean_ctor_set(v___x_2713_, 2, v___x_2711_);
lean_ctor_set(v___x_2713_, 3, v___x_2712_);
v___x_2714_ = l_Lean_Syntax_node1(v___x_2696_, v___x_2708_, v___x_2713_);
v___x_2715_ = l_Lean_Syntax_node2(v___x_2696_, v___x_2705_, v___x_2707_, v___x_2714_);
v___x_2716_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__10));
v___x_2717_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__11));
v___x_2718_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2718_, 0, v___x_2696_);
lean_ctor_set(v___x_2718_, 1, v___x_2717_);
v___x_2719_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__14));
v___x_2720_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__16));
v___x_2721_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__17));
v___x_2722_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__18));
v___x_2723_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2723_, 0, v___x_2696_);
lean_ctor_set(v___x_2723_, 1, v___x_2721_);
v___x_2724_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__20));
v___x_2725_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__21, &l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__21_once, _init_l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__21);
v___x_2726_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2726_, 0, v___x_2696_);
lean_ctor_set(v___x_2726_, 1, v___x_2703_);
lean_ctor_set(v___x_2726_, 2, v___x_2725_);
v___x_2727_ = l_Lean_Syntax_node1(v___x_2696_, v___x_2724_, v___x_2726_);
v___x_2728_ = l_Lean_Syntax_node2(v___x_2696_, v___x_2722_, v___x_2723_, v___x_2727_);
v___x_2729_ = l_Lean_Syntax_node1(v___x_2696_, v___x_2703_, v___x_2728_);
v___x_2730_ = l_Lean_Syntax_node1(v___x_2696_, v___x_2720_, v___x_2729_);
v___x_2731_ = l_Lean_Syntax_node1(v___x_2696_, v___x_2719_, v___x_2730_);
v___x_2732_ = l_Lean_Syntax_node2(v___x_2696_, v___x_2716_, v___x_2718_, v___x_2731_);
v___x_2733_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__80));
v___x_2734_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2734_, 0, v___x_2696_);
lean_ctor_set(v___x_2734_, 1, v___x_2733_);
v___x_2735_ = l_Lean_Syntax_node3(v___x_2696_, v___x_2704_, v___x_2715_, v___x_2732_, v___x_2734_);
v___x_2736_ = l_Lean_Syntax_node2(v___x_2696_, v___x_2703_, v_a_2687_, v___x_2735_);
v___x_2737_ = l_Lean_Syntax_node2(v___x_2696_, v___x_2697_, v___x_2702_, v___x_2736_);
if (v_isShared_2691_ == 0)
{
lean_ctor_set(v___x_2690_, 0, v___x_2737_);
v___x_2739_ = v___x_2690_;
goto v_reusejp_2738_;
}
else
{
lean_object* v_reuseFailAlloc_2740_; 
v_reuseFailAlloc_2740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2740_, 0, v___x_2737_);
lean_ctor_set(v_reuseFailAlloc_2740_, 1, v_a_2688_);
v___x_2739_ = v_reuseFailAlloc_2740_;
goto v_reusejp_2738_;
}
v_reusejp_2738_:
{
return v___x_2739_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___boxed(lean_object* v_n_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_){
_start:
{
lean_object* v_res_2745_; 
v_res_2745_ = l___private_Std_Time_Notation_0__Std_Time_syntaxBounded(v_n_2742_, v_a_2743_, v_a_2744_);
lean_dec_ref(v_a_2743_);
lean_dec(v_n_2742_);
return v_res_2745_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_syntaxVal___closed__1(void){
_start:
{
lean_object* v___x_2747_; lean_object* v___x_2748_; 
v___x_2747_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxVal___closed__0));
v___x_2748_ = l_String_toRawSubstring_x27(v___x_2747_);
return v___x_2748_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxVal(lean_object* v_n_2768_, lean_object* v_a_2769_, lean_object* v_a_2770_){
_start:
{
lean_object* v___x_2771_; lean_object* v_a_2772_; lean_object* v_a_2773_; lean_object* v___x_2775_; uint8_t v_isShared_2776_; uint8_t v_isSharedCheck_2794_; 
v___x_2771_ = l___private_Std_Time_Notation_0__Std_Time_syntaxInt(v_n_2768_, v_a_2769_, v_a_2770_);
v_a_2772_ = lean_ctor_get(v___x_2771_, 0);
v_a_2773_ = lean_ctor_get(v___x_2771_, 1);
v_isSharedCheck_2794_ = !lean_is_exclusive(v___x_2771_);
if (v_isSharedCheck_2794_ == 0)
{
v___x_2775_ = v___x_2771_;
v_isShared_2776_ = v_isSharedCheck_2794_;
goto v_resetjp_2774_;
}
else
{
lean_inc(v_a_2773_);
lean_inc(v_a_2772_);
lean_dec(v___x_2771_);
v___x_2775_ = lean_box(0);
v_isShared_2776_ = v_isSharedCheck_2794_;
goto v_resetjp_2774_;
}
v_resetjp_2774_:
{
lean_object* v_quotContext_2777_; lean_object* v_currMacroScope_2778_; lean_object* v_ref_2779_; uint8_t v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2792_; 
v_quotContext_2777_ = lean_ctor_get(v_a_2769_, 1);
v_currMacroScope_2778_ = lean_ctor_get(v_a_2769_, 2);
v_ref_2779_ = lean_ctor_get(v_a_2769_, 5);
v___x_2780_ = 0;
v___x_2781_ = l_Lean_SourceInfo_fromRef(v_ref_2779_, v___x_2780_);
v___x_2782_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2783_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_syntaxVal___closed__1, &l___private_Std_Time_Notation_0__Std_Time_syntaxVal___closed__1_once, _init_l___private_Std_Time_Notation_0__Std_Time_syntaxVal___closed__1);
v___x_2784_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxVal___closed__4));
lean_inc(v_currMacroScope_2778_);
lean_inc(v_quotContext_2777_);
v___x_2785_ = l_Lean_addMacroScope(v_quotContext_2777_, v___x_2784_, v_currMacroScope_2778_);
v___x_2786_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxVal___closed__8));
lean_inc_n(v___x_2781_, 2);
v___x_2787_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2787_, 0, v___x_2781_);
lean_ctor_set(v___x_2787_, 1, v___x_2783_);
lean_ctor_set(v___x_2787_, 2, v___x_2785_);
lean_ctor_set(v___x_2787_, 3, v___x_2786_);
v___x_2788_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2789_ = l_Lean_Syntax_node1(v___x_2781_, v___x_2788_, v_a_2772_);
v___x_2790_ = l_Lean_Syntax_node2(v___x_2781_, v___x_2782_, v___x_2787_, v___x_2789_);
if (v_isShared_2776_ == 0)
{
lean_ctor_set(v___x_2775_, 0, v___x_2790_);
v___x_2792_ = v___x_2775_;
goto v_reusejp_2791_;
}
else
{
lean_object* v_reuseFailAlloc_2793_; 
v_reuseFailAlloc_2793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2793_, 0, v___x_2790_);
lean_ctor_set(v_reuseFailAlloc_2793_, 1, v_a_2773_);
v___x_2792_ = v_reuseFailAlloc_2793_;
goto v_reusejp_2791_;
}
v_reusejp_2791_:
{
return v___x_2792_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxVal___boxed(lean_object* v_n_2795_, lean_object* v_a_2796_, lean_object* v_a_2797_){
_start:
{
lean_object* v_res_2798_; 
v_res_2798_ = l___private_Std_Time_Notation_0__Std_Time_syntaxVal(v_n_2795_, v_a_2796_, v_a_2797_);
lean_dec_ref(v_a_2796_);
lean_dec(v_n_2795_);
return v_res_2798_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertOffset___closed__1(void){
_start:
{
lean_object* v___x_2800_; lean_object* v___x_2801_; 
v___x_2800_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffset___closed__0));
v___x_2801_ = l_String_toRawSubstring_x27(v___x_2800_);
return v___x_2801_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffset(lean_object* v_offset_2822_, lean_object* v_a_2823_, lean_object* v_a_2824_){
_start:
{
lean_object* v___x_2825_; lean_object* v_a_2826_; lean_object* v_a_2827_; lean_object* v___x_2829_; uint8_t v_isShared_2830_; uint8_t v_isSharedCheck_2848_; 
v___x_2825_ = l___private_Std_Time_Notation_0__Std_Time_syntaxVal(v_offset_2822_, v_a_2823_, v_a_2824_);
v_a_2826_ = lean_ctor_get(v___x_2825_, 0);
v_a_2827_ = lean_ctor_get(v___x_2825_, 1);
v_isSharedCheck_2848_ = !lean_is_exclusive(v___x_2825_);
if (v_isSharedCheck_2848_ == 0)
{
v___x_2829_ = v___x_2825_;
v_isShared_2830_ = v_isSharedCheck_2848_;
goto v_resetjp_2828_;
}
else
{
lean_inc(v_a_2827_);
lean_inc(v_a_2826_);
lean_dec(v___x_2825_);
v___x_2829_ = lean_box(0);
v_isShared_2830_ = v_isSharedCheck_2848_;
goto v_resetjp_2828_;
}
v_resetjp_2828_:
{
lean_object* v_quotContext_2831_; lean_object* v_currMacroScope_2832_; lean_object* v_ref_2833_; uint8_t v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2846_; 
v_quotContext_2831_ = lean_ctor_get(v_a_2823_, 1);
v_currMacroScope_2832_ = lean_ctor_get(v_a_2823_, 2);
v_ref_2833_ = lean_ctor_get(v_a_2823_, 5);
v___x_2834_ = 0;
v___x_2835_ = l_Lean_SourceInfo_fromRef(v_ref_2833_, v___x_2834_);
v___x_2836_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2837_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertOffset___closed__1, &l___private_Std_Time_Notation_0__Std_Time_convertOffset___closed__1_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertOffset___closed__1);
v___x_2838_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffset___closed__5));
lean_inc(v_currMacroScope_2832_);
lean_inc(v_quotContext_2831_);
v___x_2839_ = l_Lean_addMacroScope(v_quotContext_2831_, v___x_2838_, v_currMacroScope_2832_);
v___x_2840_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffset___closed__9));
lean_inc_n(v___x_2835_, 2);
v___x_2841_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2841_, 0, v___x_2835_);
lean_ctor_set(v___x_2841_, 1, v___x_2837_);
lean_ctor_set(v___x_2841_, 2, v___x_2839_);
lean_ctor_set(v___x_2841_, 3, v___x_2840_);
v___x_2842_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2843_ = l_Lean_Syntax_node1(v___x_2835_, v___x_2842_, v_a_2826_);
v___x_2844_ = l_Lean_Syntax_node2(v___x_2835_, v___x_2836_, v___x_2841_, v___x_2843_);
if (v_isShared_2830_ == 0)
{
lean_ctor_set(v___x_2829_, 0, v___x_2844_);
v___x_2846_ = v___x_2829_;
goto v_reusejp_2845_;
}
else
{
lean_object* v_reuseFailAlloc_2847_; 
v_reuseFailAlloc_2847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2847_, 0, v___x_2844_);
lean_ctor_set(v_reuseFailAlloc_2847_, 1, v_a_2827_);
v___x_2846_ = v_reuseFailAlloc_2847_;
goto v_reusejp_2845_;
}
v_reusejp_2845_:
{
return v___x_2846_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffset___boxed(lean_object* v_offset_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_){
_start:
{
lean_object* v_res_2852_; 
v_res_2852_ = l___private_Std_Time_Notation_0__Std_Time_convertOffset(v_offset_2849_, v_a_2850_, v_a_2851_);
lean_dec_ref(v_a_2850_);
lean_dec(v_offset_2849_);
return v_res_2852_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__1(void){
_start:
{
lean_object* v___x_2854_; lean_object* v___x_2855_; 
v___x_2854_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__0));
v___x_2855_ = l_String_toRawSubstring_x27(v___x_2854_);
return v___x_2855_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__8(void){
_start:
{
lean_object* v___x_2873_; lean_object* v___x_2874_; 
v___x_2873_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__7));
v___x_2874_ = l_String_toRawSubstring_x27(v___x_2873_);
return v___x_2874_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertTimezone(lean_object* v_tz_2887_, lean_object* v_a_2888_, lean_object* v_a_2889_){
_start:
{
lean_object* v_offset_2890_; lean_object* v_name_2891_; lean_object* v_abbreviation_2892_; lean_object* v___x_2893_; lean_object* v_a_2894_; lean_object* v_a_2895_; lean_object* v___x_2897_; uint8_t v_isShared_2898_; uint8_t v_isSharedCheck_2924_; 
v_offset_2890_ = lean_ctor_get(v_tz_2887_, 0);
lean_inc(v_offset_2890_);
v_name_2891_ = lean_ctor_get(v_tz_2887_, 1);
lean_inc_ref(v_name_2891_);
v_abbreviation_2892_ = lean_ctor_get(v_tz_2887_, 2);
lean_inc_ref(v_abbreviation_2892_);
lean_dec_ref(v_tz_2887_);
v___x_2893_ = l___private_Std_Time_Notation_0__Std_Time_convertOffset(v_offset_2890_, v_a_2888_, v_a_2889_);
lean_dec(v_offset_2890_);
v_a_2894_ = lean_ctor_get(v___x_2893_, 0);
v_a_2895_ = lean_ctor_get(v___x_2893_, 1);
v_isSharedCheck_2924_ = !lean_is_exclusive(v___x_2893_);
if (v_isSharedCheck_2924_ == 0)
{
v___x_2897_ = v___x_2893_;
v_isShared_2898_ = v_isSharedCheck_2924_;
goto v_resetjp_2896_;
}
else
{
lean_inc(v_a_2895_);
lean_inc(v_a_2894_);
lean_dec(v___x_2893_);
v___x_2897_ = lean_box(0);
v_isShared_2898_ = v_isSharedCheck_2924_;
goto v_resetjp_2896_;
}
v_resetjp_2896_:
{
lean_object* v_quotContext_2899_; lean_object* v_currMacroScope_2900_; lean_object* v_ref_2901_; uint8_t v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2922_; 
v_quotContext_2899_ = lean_ctor_get(v_a_2888_, 1);
v_currMacroScope_2900_ = lean_ctor_get(v_a_2888_, 2);
v_ref_2901_ = lean_ctor_get(v_a_2888_, 5);
v___x_2902_ = 0;
v___x_2903_ = l_Lean_SourceInfo_fromRef(v_ref_2901_, v___x_2902_);
v___x_2904_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2905_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__1, &l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__1_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__1);
v___x_2906_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__2));
lean_inc_n(v_currMacroScope_2900_, 2);
lean_inc_n(v_quotContext_2899_, 2);
v___x_2907_ = l_Lean_addMacroScope(v_quotContext_2899_, v___x_2906_, v_currMacroScope_2900_);
v___x_2908_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__6));
lean_inc_n(v___x_2903_, 3);
v___x_2909_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2909_, 0, v___x_2903_);
lean_ctor_set(v___x_2909_, 1, v___x_2905_);
lean_ctor_set(v___x_2909_, 2, v___x_2907_);
lean_ctor_set(v___x_2909_, 3, v___x_2908_);
v___x_2910_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2911_ = lean_box(2);
v___x_2912_ = l_Lean_Syntax_mkStrLit(v_name_2891_, v___x_2911_);
v___x_2913_ = l_Lean_Syntax_mkStrLit(v_abbreviation_2892_, v___x_2911_);
v___x_2914_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__8, &l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__8_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__8);
v___x_2915_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__9));
v___x_2916_ = l_Lean_addMacroScope(v_quotContext_2899_, v___x_2915_, v_currMacroScope_2900_);
v___x_2917_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__13));
v___x_2918_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2918_, 0, v___x_2903_);
lean_ctor_set(v___x_2918_, 1, v___x_2914_);
lean_ctor_set(v___x_2918_, 2, v___x_2916_);
lean_ctor_set(v___x_2918_, 3, v___x_2917_);
v___x_2919_ = l_Lean_Syntax_node4(v___x_2903_, v___x_2910_, v_a_2894_, v___x_2912_, v___x_2913_, v___x_2918_);
v___x_2920_ = l_Lean_Syntax_node2(v___x_2903_, v___x_2904_, v___x_2909_, v___x_2919_);
if (v_isShared_2898_ == 0)
{
lean_ctor_set(v___x_2897_, 0, v___x_2920_);
v___x_2922_ = v___x_2897_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_2923_; 
v_reuseFailAlloc_2923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2923_, 0, v___x_2920_);
lean_ctor_set(v_reuseFailAlloc_2923_, 1, v_a_2895_);
v___x_2922_ = v_reuseFailAlloc_2923_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
return v___x_2922_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertTimezone___boxed(lean_object* v_tz_2925_, lean_object* v_a_2926_, lean_object* v_a_2927_){
_start:
{
lean_object* v_res_2928_; 
v_res_2928_ = l___private_Std_Time_Notation_0__Std_Time_convertTimezone(v_tz_2925_, v_a_2926_, v_a_2927_);
lean_dec_ref(v_a_2926_);
return v_res_2928_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertPlainDate___closed__1(void){
_start:
{
lean_object* v___x_2930_; lean_object* v___x_2931_; 
v___x_2930_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertPlainDate___closed__0));
v___x_2931_ = l_String_toRawSubstring_x27(v___x_2930_);
return v___x_2931_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertPlainDate(lean_object* v_d_2945_, lean_object* v_a_2946_, lean_object* v_a_2947_){
_start:
{
lean_object* v_year_2948_; lean_object* v_month_2949_; lean_object* v_day_2950_; lean_object* v___x_2951_; lean_object* v_a_2952_; lean_object* v_a_2953_; lean_object* v___x_2954_; lean_object* v_a_2955_; lean_object* v_a_2956_; lean_object* v___x_2957_; lean_object* v_a_2958_; lean_object* v_a_2959_; lean_object* v___x_2961_; uint8_t v_isShared_2962_; uint8_t v_isSharedCheck_2980_; 
v_year_2948_ = lean_ctor_get(v_d_2945_, 0);
v_month_2949_ = lean_ctor_get(v_d_2945_, 1);
v_day_2950_ = lean_ctor_get(v_d_2945_, 2);
v___x_2951_ = l___private_Std_Time_Notation_0__Std_Time_syntaxInt(v_year_2948_, v_a_2946_, v_a_2947_);
v_a_2952_ = lean_ctor_get(v___x_2951_, 0);
lean_inc(v_a_2952_);
v_a_2953_ = lean_ctor_get(v___x_2951_, 1);
lean_inc(v_a_2953_);
lean_dec_ref(v___x_2951_);
v___x_2954_ = l___private_Std_Time_Notation_0__Std_Time_syntaxBounded(v_month_2949_, v_a_2946_, v_a_2953_);
v_a_2955_ = lean_ctor_get(v___x_2954_, 0);
lean_inc(v_a_2955_);
v_a_2956_ = lean_ctor_get(v___x_2954_, 1);
lean_inc(v_a_2956_);
lean_dec_ref(v___x_2954_);
v___x_2957_ = l___private_Std_Time_Notation_0__Std_Time_syntaxBounded(v_day_2950_, v_a_2946_, v_a_2956_);
v_a_2958_ = lean_ctor_get(v___x_2957_, 0);
v_a_2959_ = lean_ctor_get(v___x_2957_, 1);
v_isSharedCheck_2980_ = !lean_is_exclusive(v___x_2957_);
if (v_isSharedCheck_2980_ == 0)
{
v___x_2961_ = v___x_2957_;
v_isShared_2962_ = v_isSharedCheck_2980_;
goto v_resetjp_2960_;
}
else
{
lean_inc(v_a_2959_);
lean_inc(v_a_2958_);
lean_dec(v___x_2957_);
v___x_2961_ = lean_box(0);
v_isShared_2962_ = v_isSharedCheck_2980_;
goto v_resetjp_2960_;
}
v_resetjp_2960_:
{
lean_object* v_quotContext_2963_; lean_object* v_currMacroScope_2964_; lean_object* v_ref_2965_; uint8_t v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2978_; 
v_quotContext_2963_ = lean_ctor_get(v_a_2946_, 1);
v_currMacroScope_2964_ = lean_ctor_get(v_a_2946_, 2);
v_ref_2965_ = lean_ctor_get(v_a_2946_, 5);
v___x_2966_ = 0;
v___x_2967_ = l_Lean_SourceInfo_fromRef(v_ref_2965_, v___x_2966_);
v___x_2968_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2969_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertPlainDate___closed__1, &l___private_Std_Time_Notation_0__Std_Time_convertPlainDate___closed__1_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertPlainDate___closed__1);
v___x_2970_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertPlainDate___closed__4));
lean_inc(v_currMacroScope_2964_);
lean_inc(v_quotContext_2963_);
v___x_2971_ = l_Lean_addMacroScope(v_quotContext_2963_, v___x_2970_, v_currMacroScope_2964_);
v___x_2972_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertPlainDate___closed__6));
lean_inc_n(v___x_2967_, 2);
v___x_2973_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2973_, 0, v___x_2967_);
lean_ctor_set(v___x_2973_, 1, v___x_2969_);
lean_ctor_set(v___x_2973_, 2, v___x_2971_);
lean_ctor_set(v___x_2973_, 3, v___x_2972_);
v___x_2974_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2975_ = l_Lean_Syntax_node3(v___x_2967_, v___x_2974_, v_a_2952_, v_a_2955_, v_a_2958_);
v___x_2976_ = l_Lean_Syntax_node2(v___x_2967_, v___x_2968_, v___x_2973_, v___x_2975_);
if (v_isShared_2962_ == 0)
{
lean_ctor_set(v___x_2961_, 0, v___x_2976_);
v___x_2978_ = v___x_2961_;
goto v_reusejp_2977_;
}
else
{
lean_object* v_reuseFailAlloc_2979_; 
v_reuseFailAlloc_2979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2979_, 0, v___x_2976_);
lean_ctor_set(v_reuseFailAlloc_2979_, 1, v_a_2959_);
v___x_2978_ = v_reuseFailAlloc_2979_;
goto v_reusejp_2977_;
}
v_reusejp_2977_:
{
return v___x_2978_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertPlainDate___boxed(lean_object* v_d_2981_, lean_object* v_a_2982_, lean_object* v_a_2983_){
_start:
{
lean_object* v_res_2984_; 
v_res_2984_ = l___private_Std_Time_Notation_0__Std_Time_convertPlainDate(v_d_2981_, v_a_2982_, v_a_2983_);
lean_dec_ref(v_a_2982_);
lean_dec_ref(v_d_2981_);
return v_res_2984_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertPlainTime___closed__1(void){
_start:
{
lean_object* v___x_2986_; lean_object* v___x_2987_; 
v___x_2986_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertPlainTime___closed__0));
v___x_2987_ = l_String_toRawSubstring_x27(v___x_2986_);
return v___x_2987_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertPlainTime(lean_object* v_d_3005_, lean_object* v_a_3006_, lean_object* v_a_3007_){
_start:
{
lean_object* v_hour_3008_; lean_object* v_minute_3009_; lean_object* v_second_3010_; lean_object* v_nanosecond_3011_; lean_object* v___x_3013_; uint8_t v_isShared_3014_; uint8_t v_isSharedCheck_3050_; 
v_hour_3008_ = lean_ctor_get(v_d_3005_, 0);
v_minute_3009_ = lean_ctor_get(v_d_3005_, 1);
v_second_3010_ = lean_ctor_get(v_d_3005_, 2);
v_nanosecond_3011_ = lean_ctor_get(v_d_3005_, 3);
v_isSharedCheck_3050_ = !lean_is_exclusive(v_d_3005_);
if (v_isSharedCheck_3050_ == 0)
{
v___x_3013_ = v_d_3005_;
v_isShared_3014_ = v_isSharedCheck_3050_;
goto v_resetjp_3012_;
}
else
{
lean_inc(v_nanosecond_3011_);
lean_inc(v_second_3010_);
lean_inc(v_minute_3009_);
lean_inc(v_hour_3008_);
lean_dec(v_d_3005_);
v___x_3013_ = lean_box(0);
v_isShared_3014_ = v_isSharedCheck_3050_;
goto v_resetjp_3012_;
}
v_resetjp_3012_:
{
lean_object* v___x_3015_; lean_object* v_a_3016_; lean_object* v_a_3017_; lean_object* v___x_3018_; lean_object* v_a_3019_; lean_object* v_a_3020_; lean_object* v___x_3021_; lean_object* v_a_3022_; lean_object* v_a_3023_; lean_object* v___x_3024_; lean_object* v_a_3025_; lean_object* v_a_3026_; lean_object* v___x_3028_; uint8_t v_isShared_3029_; uint8_t v_isSharedCheck_3049_; 
v___x_3015_ = l___private_Std_Time_Notation_0__Std_Time_syntaxBounded(v_hour_3008_, v_a_3006_, v_a_3007_);
lean_dec(v_hour_3008_);
v_a_3016_ = lean_ctor_get(v___x_3015_, 0);
lean_inc(v_a_3016_);
v_a_3017_ = lean_ctor_get(v___x_3015_, 1);
lean_inc(v_a_3017_);
lean_dec_ref(v___x_3015_);
v___x_3018_ = l___private_Std_Time_Notation_0__Std_Time_syntaxBounded(v_minute_3009_, v_a_3006_, v_a_3017_);
lean_dec(v_minute_3009_);
v_a_3019_ = lean_ctor_get(v___x_3018_, 0);
lean_inc(v_a_3019_);
v_a_3020_ = lean_ctor_get(v___x_3018_, 1);
lean_inc(v_a_3020_);
lean_dec_ref(v___x_3018_);
v___x_3021_ = l___private_Std_Time_Notation_0__Std_Time_syntaxBounded(v_second_3010_, v_a_3006_, v_a_3020_);
lean_dec(v_second_3010_);
v_a_3022_ = lean_ctor_get(v___x_3021_, 0);
lean_inc(v_a_3022_);
v_a_3023_ = lean_ctor_get(v___x_3021_, 1);
lean_inc(v_a_3023_);
lean_dec_ref(v___x_3021_);
v___x_3024_ = l___private_Std_Time_Notation_0__Std_Time_syntaxBounded(v_nanosecond_3011_, v_a_3006_, v_a_3023_);
lean_dec(v_nanosecond_3011_);
v_a_3025_ = lean_ctor_get(v___x_3024_, 0);
v_a_3026_ = lean_ctor_get(v___x_3024_, 1);
v_isSharedCheck_3049_ = !lean_is_exclusive(v___x_3024_);
if (v_isSharedCheck_3049_ == 0)
{
v___x_3028_ = v___x_3024_;
v_isShared_3029_ = v_isSharedCheck_3049_;
goto v_resetjp_3027_;
}
else
{
lean_inc(v_a_3026_);
lean_inc(v_a_3025_);
lean_dec(v___x_3024_);
v___x_3028_ = lean_box(0);
v_isShared_3029_ = v_isSharedCheck_3049_;
goto v_resetjp_3027_;
}
v_resetjp_3027_:
{
lean_object* v_quotContext_3030_; lean_object* v_currMacroScope_3031_; lean_object* v_ref_3032_; uint8_t v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3041_; 
v_quotContext_3030_ = lean_ctor_get(v_a_3006_, 1);
v_currMacroScope_3031_ = lean_ctor_get(v_a_3006_, 2);
v_ref_3032_ = lean_ctor_get(v_a_3006_, 5);
v___x_3033_ = 0;
v___x_3034_ = l_Lean_SourceInfo_fromRef(v_ref_3032_, v___x_3033_);
v___x_3035_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_3036_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertPlainTime___closed__1, &l___private_Std_Time_Notation_0__Std_Time_convertPlainTime___closed__1_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertPlainTime___closed__1);
v___x_3037_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertPlainTime___closed__3));
lean_inc(v_currMacroScope_3031_);
lean_inc(v_quotContext_3030_);
v___x_3038_ = l_Lean_addMacroScope(v_quotContext_3030_, v___x_3037_, v_currMacroScope_3031_);
v___x_3039_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertPlainTime___closed__7));
lean_inc(v___x_3034_);
if (v_isShared_3014_ == 0)
{
lean_ctor_set_tag(v___x_3013_, 3);
lean_ctor_set(v___x_3013_, 3, v___x_3039_);
lean_ctor_set(v___x_3013_, 2, v___x_3038_);
lean_ctor_set(v___x_3013_, 1, v___x_3036_);
lean_ctor_set(v___x_3013_, 0, v___x_3034_);
v___x_3041_ = v___x_3013_;
goto v_reusejp_3040_;
}
else
{
lean_object* v_reuseFailAlloc_3048_; 
v_reuseFailAlloc_3048_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3048_, 0, v___x_3034_);
lean_ctor_set(v_reuseFailAlloc_3048_, 1, v___x_3036_);
lean_ctor_set(v_reuseFailAlloc_3048_, 2, v___x_3038_);
lean_ctor_set(v_reuseFailAlloc_3048_, 3, v___x_3039_);
v___x_3041_ = v_reuseFailAlloc_3048_;
goto v_reusejp_3040_;
}
v_reusejp_3040_:
{
lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3046_; 
v___x_3042_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
lean_inc(v___x_3034_);
v___x_3043_ = l_Lean_Syntax_node4(v___x_3034_, v___x_3042_, v_a_3016_, v_a_3019_, v_a_3022_, v_a_3025_);
v___x_3044_ = l_Lean_Syntax_node2(v___x_3034_, v___x_3035_, v___x_3041_, v___x_3043_);
if (v_isShared_3029_ == 0)
{
lean_ctor_set(v___x_3028_, 0, v___x_3044_);
v___x_3046_ = v___x_3028_;
goto v_reusejp_3045_;
}
else
{
lean_object* v_reuseFailAlloc_3047_; 
v_reuseFailAlloc_3047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3047_, 0, v___x_3044_);
lean_ctor_set(v_reuseFailAlloc_3047_, 1, v_a_3026_);
v___x_3046_ = v_reuseFailAlloc_3047_;
goto v_reusejp_3045_;
}
v_reusejp_3045_:
{
return v___x_3046_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertPlainTime___boxed(lean_object* v_d_3051_, lean_object* v_a_3052_, lean_object* v_a_3053_){
_start:
{
lean_object* v_res_3054_; 
v_res_3054_ = l___private_Std_Time_Notation_0__Std_Time_convertPlainTime(v_d_3051_, v_a_3052_, v_a_3053_);
lean_dec_ref(v_a_3052_);
return v_res_3054_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime___closed__1(void){
_start:
{
lean_object* v___x_3056_; lean_object* v___x_3057_; 
v___x_3056_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime___closed__0));
v___x_3057_ = l_String_toRawSubstring_x27(v___x_3056_);
return v___x_3057_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime(lean_object* v_d_3075_, lean_object* v_a_3076_, lean_object* v_a_3077_){
_start:
{
lean_object* v_date_3078_; lean_object* v_time_3079_; lean_object* v___x_3080_; lean_object* v_a_3081_; lean_object* v_a_3082_; lean_object* v___x_3083_; lean_object* v_a_3084_; lean_object* v_a_3085_; lean_object* v___x_3087_; uint8_t v_isShared_3088_; uint8_t v_isSharedCheck_3106_; 
v_date_3078_ = lean_ctor_get(v_d_3075_, 0);
lean_inc_ref(v_date_3078_);
v_time_3079_ = lean_ctor_get(v_d_3075_, 1);
lean_inc_ref(v_time_3079_);
lean_dec_ref(v_d_3075_);
v___x_3080_ = l___private_Std_Time_Notation_0__Std_Time_convertPlainDate(v_date_3078_, v_a_3076_, v_a_3077_);
lean_dec_ref(v_date_3078_);
v_a_3081_ = lean_ctor_get(v___x_3080_, 0);
lean_inc(v_a_3081_);
v_a_3082_ = lean_ctor_get(v___x_3080_, 1);
lean_inc(v_a_3082_);
lean_dec_ref(v___x_3080_);
v___x_3083_ = l___private_Std_Time_Notation_0__Std_Time_convertPlainTime(v_time_3079_, v_a_3076_, v_a_3082_);
v_a_3084_ = lean_ctor_get(v___x_3083_, 0);
v_a_3085_ = lean_ctor_get(v___x_3083_, 1);
v_isSharedCheck_3106_ = !lean_is_exclusive(v___x_3083_);
if (v_isSharedCheck_3106_ == 0)
{
v___x_3087_ = v___x_3083_;
v_isShared_3088_ = v_isSharedCheck_3106_;
goto v_resetjp_3086_;
}
else
{
lean_inc(v_a_3085_);
lean_inc(v_a_3084_);
lean_dec(v___x_3083_);
v___x_3087_ = lean_box(0);
v_isShared_3088_ = v_isSharedCheck_3106_;
goto v_resetjp_3086_;
}
v_resetjp_3086_:
{
lean_object* v_quotContext_3089_; lean_object* v_currMacroScope_3090_; lean_object* v_ref_3091_; uint8_t v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3104_; 
v_quotContext_3089_ = lean_ctor_get(v_a_3076_, 1);
v_currMacroScope_3090_ = lean_ctor_get(v_a_3076_, 2);
v_ref_3091_ = lean_ctor_get(v_a_3076_, 5);
v___x_3092_ = 0;
v___x_3093_ = l_Lean_SourceInfo_fromRef(v_ref_3091_, v___x_3092_);
v___x_3094_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_3095_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime___closed__1, &l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime___closed__1_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime___closed__1);
v___x_3096_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime___closed__3));
lean_inc(v_currMacroScope_3090_);
lean_inc(v_quotContext_3089_);
v___x_3097_ = l_Lean_addMacroScope(v_quotContext_3089_, v___x_3096_, v_currMacroScope_3090_);
v___x_3098_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime___closed__7));
lean_inc_n(v___x_3093_, 2);
v___x_3099_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3099_, 0, v___x_3093_);
lean_ctor_set(v___x_3099_, 1, v___x_3095_);
lean_ctor_set(v___x_3099_, 2, v___x_3097_);
lean_ctor_set(v___x_3099_, 3, v___x_3098_);
v___x_3100_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_3101_ = l_Lean_Syntax_node2(v___x_3093_, v___x_3100_, v_a_3081_, v_a_3084_);
v___x_3102_ = l_Lean_Syntax_node2(v___x_3093_, v___x_3094_, v___x_3099_, v___x_3101_);
if (v_isShared_3088_ == 0)
{
lean_ctor_set(v___x_3087_, 0, v___x_3102_);
v___x_3104_ = v___x_3087_;
goto v_reusejp_3103_;
}
else
{
lean_object* v_reuseFailAlloc_3105_; 
v_reuseFailAlloc_3105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3105_, 0, v___x_3102_);
lean_ctor_set(v_reuseFailAlloc_3105_, 1, v_a_3085_);
v___x_3104_ = v_reuseFailAlloc_3105_;
goto v_reusejp_3103_;
}
v_reusejp_3103_:
{
return v___x_3104_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime___boxed(lean_object* v_d_3107_, lean_object* v_a_3108_, lean_object* v_a_3109_){
_start:
{
lean_object* v_res_3110_; 
v_res_3110_ = l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime(v_d_3107_, v_a_3108_, v_a_3109_);
lean_dec_ref(v_a_3108_);
return v_res_3110_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__1(void){
_start:
{
lean_object* v___x_3112_; lean_object* v___x_3113_; 
v___x_3112_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__0));
v___x_3113_ = l_String_toRawSubstring_x27(v___x_3112_);
return v___x_3113_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__8(void){
_start:
{
lean_object* v___x_3128_; lean_object* v___x_3129_; 
v___x_3128_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__7));
v___x_3129_ = l_String_toRawSubstring_x27(v___x_3128_);
return v___x_3129_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__21(void){
_start:
{
lean_object* v___x_3156_; lean_object* v___x_3157_; 
v___x_3156_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__20));
v___x_3157_ = l_String_toRawSubstring_x27(v___x_3156_);
return v___x_3157_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertDateTime(lean_object* v_d_3164_, uint8_t v_identifier_3165_, lean_object* v_a_3166_, lean_object* v_a_3167_){
_start:
{
lean_object* v_date_3168_; lean_object* v_timezone_3169_; lean_object* v___x_3171_; uint8_t v_isShared_3172_; uint8_t v_isSharedCheck_3263_; 
v_date_3168_ = lean_ctor_get(v_d_3164_, 0);
v_timezone_3169_ = lean_ctor_get(v_d_3164_, 3);
v_isSharedCheck_3263_ = !lean_is_exclusive(v_d_3164_);
if (v_isSharedCheck_3263_ == 0)
{
lean_object* v_unused_3264_; lean_object* v_unused_3265_; 
v_unused_3264_ = lean_ctor_get(v_d_3164_, 2);
lean_dec(v_unused_3264_);
v_unused_3265_ = lean_ctor_get(v_d_3164_, 1);
lean_dec(v_unused_3265_);
v___x_3171_ = v_d_3164_;
v_isShared_3172_ = v_isSharedCheck_3263_;
goto v_resetjp_3170_;
}
else
{
lean_inc(v_timezone_3169_);
lean_inc(v_date_3168_);
lean_dec(v_d_3164_);
v___x_3171_ = lean_box(0);
v_isShared_3172_ = v_isSharedCheck_3263_;
goto v_resetjp_3170_;
}
v_resetjp_3170_:
{
lean_object* v___x_3173_; lean_object* v___x_3174_; 
v___x_3173_ = lean_thunk_get_own(v_date_3168_);
lean_dec_ref(v_date_3168_);
v___x_3174_ = l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime(v___x_3173_, v_a_3166_, v_a_3167_);
if (v_identifier_3165_ == 0)
{
lean_object* v_a_3175_; lean_object* v_a_3176_; lean_object* v___x_3177_; lean_object* v_a_3178_; lean_object* v_a_3179_; lean_object* v___x_3181_; uint8_t v_isShared_3182_; uint8_t v_isSharedCheck_3223_; 
v_a_3175_ = lean_ctor_get(v___x_3174_, 0);
lean_inc(v_a_3175_);
v_a_3176_ = lean_ctor_get(v___x_3174_, 1);
lean_inc(v_a_3176_);
lean_dec_ref(v___x_3174_);
v___x_3177_ = l___private_Std_Time_Notation_0__Std_Time_convertTimezone(v_timezone_3169_, v_a_3166_, v_a_3176_);
v_a_3178_ = lean_ctor_get(v___x_3177_, 0);
v_a_3179_ = lean_ctor_get(v___x_3177_, 1);
v_isSharedCheck_3223_ = !lean_is_exclusive(v___x_3177_);
if (v_isSharedCheck_3223_ == 0)
{
v___x_3181_ = v___x_3177_;
v_isShared_3182_ = v_isSharedCheck_3223_;
goto v_resetjp_3180_;
}
else
{
lean_inc(v_a_3179_);
lean_inc(v_a_3178_);
lean_dec(v___x_3177_);
v___x_3181_ = lean_box(0);
v_isShared_3182_ = v_isSharedCheck_3223_;
goto v_resetjp_3180_;
}
v_resetjp_3180_:
{
lean_object* v_quotContext_3183_; lean_object* v_currMacroScope_3184_; lean_object* v_ref_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3193_; 
v_quotContext_3183_ = lean_ctor_get(v_a_3166_, 1);
v_currMacroScope_3184_ = lean_ctor_get(v_a_3166_, 2);
v_ref_3185_ = lean_ctor_get(v_a_3166_, 5);
v___x_3186_ = l_Lean_SourceInfo_fromRef(v_ref_3185_, v_identifier_3165_);
v___x_3187_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_3188_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__1, &l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__1_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__1);
v___x_3189_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__4));
lean_inc(v_currMacroScope_3184_);
lean_inc(v_quotContext_3183_);
v___x_3190_ = l_Lean_addMacroScope(v_quotContext_3183_, v___x_3189_, v_currMacroScope_3184_);
v___x_3191_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__6));
lean_inc(v___x_3186_);
if (v_isShared_3172_ == 0)
{
lean_ctor_set_tag(v___x_3171_, 3);
lean_ctor_set(v___x_3171_, 3, v___x_3191_);
lean_ctor_set(v___x_3171_, 2, v___x_3190_);
lean_ctor_set(v___x_3171_, 1, v___x_3188_);
lean_ctor_set(v___x_3171_, 0, v___x_3186_);
v___x_3193_ = v___x_3171_;
goto v_reusejp_3192_;
}
else
{
lean_object* v_reuseFailAlloc_3222_; 
v_reuseFailAlloc_3222_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3222_, 0, v___x_3186_);
lean_ctor_set(v_reuseFailAlloc_3222_, 1, v___x_3188_);
lean_ctor_set(v_reuseFailAlloc_3222_, 2, v___x_3190_);
lean_ctor_set(v_reuseFailAlloc_3222_, 3, v___x_3191_);
v___x_3193_ = v_reuseFailAlloc_3222_;
goto v_reusejp_3192_;
}
v_reusejp_3192_:
{
lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3220_; 
v___x_3194_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_3195_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__50));
v___x_3196_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__52));
v___x_3197_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__53));
lean_inc_n(v___x_3186_, 10);
v___x_3198_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3198_, 0, v___x_3186_);
lean_ctor_set(v___x_3198_, 1, v___x_3197_);
v___x_3199_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__55));
v___x_3200_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__57, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__57_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__57);
v___x_3201_ = lean_box(0);
lean_inc_n(v_currMacroScope_3184_, 2);
lean_inc_n(v_quotContext_3183_, 2);
v___x_3202_ = l_Lean_addMacroScope(v_quotContext_3183_, v___x_3201_, v_currMacroScope_3184_);
v___x_3203_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__73));
v___x_3204_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3204_, 0, v___x_3186_);
lean_ctor_set(v___x_3204_, 1, v___x_3200_);
lean_ctor_set(v___x_3204_, 2, v___x_3202_);
lean_ctor_set(v___x_3204_, 3, v___x_3203_);
v___x_3205_ = l_Lean_Syntax_node1(v___x_3186_, v___x_3199_, v___x_3204_);
v___x_3206_ = l_Lean_Syntax_node2(v___x_3186_, v___x_3196_, v___x_3198_, v___x_3205_);
v___x_3207_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__8, &l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__8_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__8);
v___x_3208_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__11));
v___x_3209_ = l_Lean_addMacroScope(v_quotContext_3183_, v___x_3208_, v_currMacroScope_3184_);
v___x_3210_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__13));
v___x_3211_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3211_, 0, v___x_3186_);
lean_ctor_set(v___x_3211_, 1, v___x_3207_);
lean_ctor_set(v___x_3211_, 2, v___x_3209_);
lean_ctor_set(v___x_3211_, 3, v___x_3210_);
v___x_3212_ = l_Lean_Syntax_node1(v___x_3186_, v___x_3194_, v_a_3178_);
v___x_3213_ = l_Lean_Syntax_node2(v___x_3186_, v___x_3187_, v___x_3211_, v___x_3212_);
v___x_3214_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__80));
v___x_3215_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3215_, 0, v___x_3186_);
lean_ctor_set(v___x_3215_, 1, v___x_3214_);
v___x_3216_ = l_Lean_Syntax_node3(v___x_3186_, v___x_3195_, v___x_3206_, v___x_3213_, v___x_3215_);
v___x_3217_ = l_Lean_Syntax_node2(v___x_3186_, v___x_3194_, v_a_3175_, v___x_3216_);
v___x_3218_ = l_Lean_Syntax_node2(v___x_3186_, v___x_3187_, v___x_3193_, v___x_3217_);
if (v_isShared_3182_ == 0)
{
lean_ctor_set(v___x_3181_, 0, v___x_3218_);
v___x_3220_ = v___x_3181_;
goto v_reusejp_3219_;
}
else
{
lean_object* v_reuseFailAlloc_3221_; 
v_reuseFailAlloc_3221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3221_, 0, v___x_3218_);
lean_ctor_set(v_reuseFailAlloc_3221_, 1, v_a_3179_);
v___x_3220_ = v_reuseFailAlloc_3221_;
goto v_reusejp_3219_;
}
v_reusejp_3219_:
{
return v___x_3220_;
}
}
}
}
else
{
lean_object* v_a_3224_; lean_object* v_a_3225_; lean_object* v___x_3227_; uint8_t v_isShared_3228_; uint8_t v_isSharedCheck_3262_; 
v_a_3224_ = lean_ctor_get(v___x_3174_, 0);
v_a_3225_ = lean_ctor_get(v___x_3174_, 1);
v_isSharedCheck_3262_ = !lean_is_exclusive(v___x_3174_);
if (v_isSharedCheck_3262_ == 0)
{
v___x_3227_ = v___x_3174_;
v_isShared_3228_ = v_isSharedCheck_3262_;
goto v_resetjp_3226_;
}
else
{
lean_inc(v_a_3225_);
lean_inc(v_a_3224_);
lean_dec(v___x_3174_);
v___x_3227_ = lean_box(0);
v_isShared_3228_ = v_isSharedCheck_3262_;
goto v_resetjp_3226_;
}
v_resetjp_3226_:
{
lean_object* v_quotContext_3229_; lean_object* v_currMacroScope_3230_; lean_object* v_ref_3231_; uint8_t v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3240_; 
v_quotContext_3229_ = lean_ctor_get(v_a_3166_, 1);
v_currMacroScope_3230_ = lean_ctor_get(v_a_3166_, 2);
v_ref_3231_ = lean_ctor_get(v_a_3166_, 5);
v___x_3232_ = 0;
v___x_3233_ = l_Lean_SourceInfo_fromRef(v_ref_3231_, v___x_3232_);
v___x_3234_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_3235_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__1, &l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__1_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__1);
v___x_3236_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__4));
lean_inc(v_currMacroScope_3230_);
lean_inc(v_quotContext_3229_);
v___x_3237_ = l_Lean_addMacroScope(v_quotContext_3229_, v___x_3236_, v_currMacroScope_3230_);
v___x_3238_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__6));
lean_inc(v___x_3233_);
if (v_isShared_3172_ == 0)
{
lean_ctor_set_tag(v___x_3171_, 3);
lean_ctor_set(v___x_3171_, 3, v___x_3238_);
lean_ctor_set(v___x_3171_, 2, v___x_3237_);
lean_ctor_set(v___x_3171_, 1, v___x_3235_);
lean_ctor_set(v___x_3171_, 0, v___x_3233_);
v___x_3240_ = v___x_3171_;
goto v_reusejp_3239_;
}
else
{
lean_object* v_reuseFailAlloc_3261_; 
v_reuseFailAlloc_3261_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3261_, 0, v___x_3233_);
lean_ctor_set(v_reuseFailAlloc_3261_, 1, v___x_3235_);
lean_ctor_set(v_reuseFailAlloc_3261_, 2, v___x_3237_);
lean_ctor_set(v_reuseFailAlloc_3261_, 3, v___x_3238_);
v___x_3240_ = v_reuseFailAlloc_3261_;
goto v_reusejp_3239_;
}
v_reusejp_3239_:
{
lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v_name_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3259_; 
v___x_3241_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
lean_inc_n(v___x_3233_, 6);
v___x_3242_ = l_Lean_Syntax_node1(v___x_3233_, v___x_3241_, v_a_3224_);
v___x_3243_ = l_Lean_Syntax_node2(v___x_3233_, v___x_3234_, v___x_3240_, v___x_3242_);
v_name_3244_ = lean_ctor_get(v_timezone_3169_, 1);
lean_inc_ref(v_name_3244_);
lean_dec_ref(v_timezone_3169_);
v___x_3245_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__14));
v___x_3246_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3246_, 0, v___x_3233_);
lean_ctor_set(v___x_3246_, 1, v___x_3245_);
v___x_3247_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__17));
lean_inc(v_currMacroScope_3230_);
lean_inc(v_quotContext_3229_);
v___x_3248_ = l_Lean_addMacroScope(v_quotContext_3229_, v___x_3247_, v_currMacroScope_3230_);
v___x_3249_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__19));
v___x_3250_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__21, &l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__21_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__21);
v___x_3251_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__23));
v___x_3252_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3252_, 0, v___x_3233_);
lean_ctor_set(v___x_3252_, 1, v___x_3250_);
lean_ctor_set(v___x_3252_, 2, v___x_3248_);
lean_ctor_set(v___x_3252_, 3, v___x_3251_);
v___x_3253_ = lean_box(2);
v___x_3254_ = l_Lean_Syntax_mkStrLit(v_name_3244_, v___x_3253_);
v___x_3255_ = l_Lean_Syntax_node1(v___x_3233_, v___x_3241_, v___x_3254_);
v___x_3256_ = l_Lean_Syntax_node2(v___x_3233_, v___x_3234_, v___x_3252_, v___x_3255_);
v___x_3257_ = l_Lean_Syntax_node3(v___x_3233_, v___x_3249_, v___x_3243_, v___x_3246_, v___x_3256_);
if (v_isShared_3228_ == 0)
{
lean_ctor_set(v___x_3227_, 0, v___x_3257_);
v___x_3259_ = v___x_3227_;
goto v_reusejp_3258_;
}
else
{
lean_object* v_reuseFailAlloc_3260_; 
v_reuseFailAlloc_3260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3260_, 0, v___x_3257_);
lean_ctor_set(v_reuseFailAlloc_3260_, 1, v_a_3225_);
v___x_3259_ = v_reuseFailAlloc_3260_;
goto v_reusejp_3258_;
}
v_reusejp_3258_:
{
return v___x_3259_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertDateTime___boxed(lean_object* v_d_3266_, lean_object* v_identifier_3267_, lean_object* v_a_3268_, lean_object* v_a_3269_){
_start:
{
uint8_t v_identifier_boxed_3270_; lean_object* v_res_3271_; 
v_identifier_boxed_3270_ = lean_unbox(v_identifier_3267_);
v_res_3271_ = l___private_Std_Time_Notation_0__Std_Time_convertDateTime(v_d_3266_, v_identifier_boxed_3270_, v_a_3268_, v_a_3269_);
lean_dec_ref(v_a_3268_);
return v_res_3271_;
}
}
LEAN_EXPORT lean_object* l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termZoned_x28___x29__1(lean_object* v_x_3437_, lean_object* v_a_3438_, lean_object* v_a_3439_){
_start:
{
lean_object* v___x_3440_; uint8_t v___x_3441_; 
v___x_3440_ = ((lean_object*)(l_Std_Time_termZoned_x28___x29___closed__1));
lean_inc(v_x_3437_);
v___x_3441_ = l_Lean_Syntax_isOfKind(v_x_3437_, v___x_3440_);
if (v___x_3441_ == 0)
{
lean_object* v___x_3442_; lean_object* v___x_3443_; 
lean_dec(v_x_3437_);
v___x_3442_ = lean_box(1);
v___x_3443_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3443_, 0, v___x_3442_);
lean_ctor_set(v___x_3443_, 1, v_a_3439_);
return v___x_3443_;
}
else
{
lean_object* v___x_3444_; lean_object* v_date_3445_; lean_object* v___x_3446_; uint8_t v___x_3447_; 
v___x_3444_ = lean_unsigned_to_nat(1u);
v_date_3445_ = l_Lean_Syntax_getArg(v_x_3437_, v___x_3444_);
lean_dec(v_x_3437_);
v___x_3446_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxString___closed__1));
lean_inc(v_date_3445_);
v___x_3447_ = l_Lean_Syntax_isOfKind(v_date_3445_, v___x_3446_);
if (v___x_3447_ == 0)
{
lean_object* v___x_3448_; lean_object* v___x_3449_; 
lean_dec(v_date_3445_);
v___x_3448_ = lean_box(1);
v___x_3449_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3449_, 0, v___x_3448_);
lean_ctor_set(v___x_3449_, 1, v_a_3439_);
return v___x_3449_;
}
else
{
lean_object* v___x_3450_; lean_object* v___x_3451_; 
v___x_3450_ = l_Lean_TSyntax_getString(v_date_3445_);
lean_inc_ref(v___x_3450_);
v___x_3451_ = l_Std_Time_DateTime_fromLeanDateTimeWithZoneString(v___x_3450_);
if (lean_obj_tag(v___x_3451_) == 0)
{
lean_object* v___x_3452_; 
lean_dec_ref_known(v___x_3451_, 1);
v___x_3452_ = l_Std_Time_DateTime_fromLeanDateTimeWithIdentifierString(v___x_3450_);
if (lean_obj_tag(v___x_3452_) == 0)
{
lean_object* v_a_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; 
v_a_3453_ = lean_ctor_get(v___x_3452_, 0);
lean_inc(v_a_3453_);
lean_dec_ref_known(v___x_3452_, 1);
v___x_3454_ = ((lean_object*)(l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termZoned_x28___x29__1___closed__0));
v___x_3455_ = lean_string_append(v___x_3454_, v_a_3453_);
lean_dec(v_a_3453_);
v___x_3456_ = l_Lean_Macro_throwErrorAt___redArg(v_date_3445_, v___x_3455_, v_a_3438_, v_a_3439_);
lean_dec(v_date_3445_);
return v___x_3456_;
}
else
{
lean_object* v_a_3457_; lean_object* v___x_3458_; lean_object* v_a_3459_; lean_object* v_a_3460_; lean_object* v___x_3462_; uint8_t v_isShared_3463_; uint8_t v_isSharedCheck_3467_; 
lean_dec(v_date_3445_);
v_a_3457_ = lean_ctor_get(v___x_3452_, 0);
lean_inc(v_a_3457_);
lean_dec_ref_known(v___x_3452_, 1);
v___x_3458_ = l___private_Std_Time_Notation_0__Std_Time_convertDateTime(v_a_3457_, v___x_3447_, v_a_3438_, v_a_3439_);
v_a_3459_ = lean_ctor_get(v___x_3458_, 0);
v_a_3460_ = lean_ctor_get(v___x_3458_, 1);
v_isSharedCheck_3467_ = !lean_is_exclusive(v___x_3458_);
if (v_isSharedCheck_3467_ == 0)
{
v___x_3462_ = v___x_3458_;
v_isShared_3463_ = v_isSharedCheck_3467_;
goto v_resetjp_3461_;
}
else
{
lean_inc(v_a_3460_);
lean_inc(v_a_3459_);
lean_dec(v___x_3458_);
v___x_3462_ = lean_box(0);
v_isShared_3463_ = v_isSharedCheck_3467_;
goto v_resetjp_3461_;
}
v_resetjp_3461_:
{
lean_object* v___x_3465_; 
if (v_isShared_3463_ == 0)
{
v___x_3465_ = v___x_3462_;
goto v_reusejp_3464_;
}
else
{
lean_object* v_reuseFailAlloc_3466_; 
v_reuseFailAlloc_3466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3466_, 0, v_a_3459_);
lean_ctor_set(v_reuseFailAlloc_3466_, 1, v_a_3460_);
v___x_3465_ = v_reuseFailAlloc_3466_;
goto v_reusejp_3464_;
}
v_reusejp_3464_:
{
return v___x_3465_;
}
}
}
}
else
{
lean_object* v_a_3468_; uint8_t v___x_3469_; lean_object* v___x_3470_; lean_object* v_a_3471_; lean_object* v_a_3472_; lean_object* v___x_3474_; uint8_t v_isShared_3475_; uint8_t v_isSharedCheck_3479_; 
lean_dec_ref(v___x_3450_);
lean_dec(v_date_3445_);
v_a_3468_ = lean_ctor_get(v___x_3451_, 0);
lean_inc(v_a_3468_);
lean_dec_ref_known(v___x_3451_, 1);
v___x_3469_ = 0;
v___x_3470_ = l___private_Std_Time_Notation_0__Std_Time_convertDateTime(v_a_3468_, v___x_3469_, v_a_3438_, v_a_3439_);
v_a_3471_ = lean_ctor_get(v___x_3470_, 0);
v_a_3472_ = lean_ctor_get(v___x_3470_, 1);
v_isSharedCheck_3479_ = !lean_is_exclusive(v___x_3470_);
if (v_isSharedCheck_3479_ == 0)
{
v___x_3474_ = v___x_3470_;
v_isShared_3475_ = v_isSharedCheck_3479_;
goto v_resetjp_3473_;
}
else
{
lean_inc(v_a_3472_);
lean_inc(v_a_3471_);
lean_dec(v___x_3470_);
v___x_3474_ = lean_box(0);
v_isShared_3475_ = v_isSharedCheck_3479_;
goto v_resetjp_3473_;
}
v_resetjp_3473_:
{
lean_object* v___x_3477_; 
if (v_isShared_3475_ == 0)
{
v___x_3477_ = v___x_3474_;
goto v_reusejp_3476_;
}
else
{
lean_object* v_reuseFailAlloc_3478_; 
v_reuseFailAlloc_3478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3478_, 0, v_a_3471_);
lean_ctor_set(v_reuseFailAlloc_3478_, 1, v_a_3472_);
v___x_3477_ = v_reuseFailAlloc_3478_;
goto v_reusejp_3476_;
}
v_reusejp_3476_:
{
return v___x_3477_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termZoned_x28___x29__1___boxed(lean_object* v_x_3480_, lean_object* v_a_3481_, lean_object* v_a_3482_){
_start:
{
lean_object* v_res_3483_; 
v_res_3483_ = l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termZoned_x28___x29__1(v_x_3480_, v_a_3481_, v_a_3482_);
lean_dec_ref(v_a_3481_);
return v_res_3483_;
}
}
LEAN_EXPORT lean_object* l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termZoned_x28___x2c___x29__1(lean_object* v_x_3484_, lean_object* v_a_3485_, lean_object* v_a_3486_){
_start:
{
lean_object* v___x_3487_; uint8_t v___x_3488_; 
v___x_3487_ = ((lean_object*)(l_Std_Time_termZoned_x28___x2c___x29___closed__1));
lean_inc(v_x_3484_);
v___x_3488_ = l_Lean_Syntax_isOfKind(v_x_3484_, v___x_3487_);
if (v___x_3488_ == 0)
{
lean_object* v___x_3489_; lean_object* v___x_3490_; 
lean_dec(v_x_3484_);
v___x_3489_ = lean_box(1);
v___x_3490_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3490_, 0, v___x_3489_);
lean_ctor_set(v___x_3490_, 1, v_a_3486_);
return v___x_3490_;
}
else
{
lean_object* v___x_3491_; lean_object* v_date_3492_; lean_object* v___x_3493_; uint8_t v___x_3494_; 
v___x_3491_ = lean_unsigned_to_nat(1u);
v_date_3492_ = l_Lean_Syntax_getArg(v_x_3484_, v___x_3491_);
v___x_3493_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxString___closed__1));
lean_inc(v_date_3492_);
v___x_3494_ = l_Lean_Syntax_isOfKind(v_date_3492_, v___x_3493_);
if (v___x_3494_ == 0)
{
lean_object* v___x_3495_; lean_object* v___x_3496_; 
lean_dec(v_date_3492_);
lean_dec(v_x_3484_);
v___x_3495_ = lean_box(1);
v___x_3496_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3496_, 0, v___x_3495_);
lean_ctor_set(v___x_3496_, 1, v_a_3486_);
return v___x_3496_;
}
else
{
lean_object* v___x_3497_; lean_object* v___x_3498_; 
v___x_3497_ = l_Lean_TSyntax_getString(v_date_3492_);
v___x_3498_ = l_Std_Time_PlainDateTime_fromLeanDateTimeString(v___x_3497_);
if (lean_obj_tag(v___x_3498_) == 0)
{
lean_object* v_a_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; 
lean_dec(v_x_3484_);
v_a_3499_ = lean_ctor_get(v___x_3498_, 0);
lean_inc(v_a_3499_);
lean_dec_ref_known(v___x_3498_, 1);
v___x_3500_ = ((lean_object*)(l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termZoned_x28___x29__1___closed__0));
v___x_3501_ = lean_string_append(v___x_3500_, v_a_3499_);
lean_dec(v_a_3499_);
v___x_3502_ = l_Lean_Macro_throwErrorAt___redArg(v_date_3492_, v___x_3501_, v_a_3485_, v_a_3486_);
lean_dec(v_date_3492_);
return v___x_3502_;
}
else
{
lean_object* v_a_3503_; lean_object* v___x_3504_; lean_object* v_a_3505_; lean_object* v_a_3506_; lean_object* v___x_3508_; uint8_t v_isShared_3509_; uint8_t v_isSharedCheck_3529_; 
lean_dec(v_date_3492_);
v_a_3503_ = lean_ctor_get(v___x_3498_, 0);
lean_inc(v_a_3503_);
lean_dec_ref_known(v___x_3498_, 1);
v___x_3504_ = l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime(v_a_3503_, v_a_3485_, v_a_3486_);
v_a_3505_ = lean_ctor_get(v___x_3504_, 0);
v_a_3506_ = lean_ctor_get(v___x_3504_, 1);
v_isSharedCheck_3529_ = !lean_is_exclusive(v___x_3504_);
if (v_isSharedCheck_3529_ == 0)
{
v___x_3508_ = v___x_3504_;
v_isShared_3509_ = v_isSharedCheck_3529_;
goto v_resetjp_3507_;
}
else
{
lean_inc(v_a_3506_);
lean_inc(v_a_3505_);
lean_dec(v___x_3504_);
v___x_3508_ = lean_box(0);
v_isShared_3509_ = v_isSharedCheck_3529_;
goto v_resetjp_3507_;
}
v_resetjp_3507_:
{
lean_object* v_quotContext_3510_; lean_object* v_currMacroScope_3511_; lean_object* v_ref_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; uint8_t v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3527_; 
v_quotContext_3510_ = lean_ctor_get(v_a_3485_, 1);
v_currMacroScope_3511_ = lean_ctor_get(v_a_3485_, 2);
v_ref_3512_ = lean_ctor_get(v_a_3485_, 5);
v___x_3513_ = lean_unsigned_to_nat(3u);
v___x_3514_ = l_Lean_Syntax_getArg(v_x_3484_, v___x_3513_);
lean_dec(v_x_3484_);
v___x_3515_ = 0;
v___x_3516_ = l_Lean_SourceInfo_fromRef(v_ref_3512_, v___x_3515_);
v___x_3517_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_3518_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__1, &l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__1_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__1);
v___x_3519_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__4));
lean_inc(v_currMacroScope_3511_);
lean_inc(v_quotContext_3510_);
v___x_3520_ = l_Lean_addMacroScope(v_quotContext_3510_, v___x_3519_, v_currMacroScope_3511_);
v___x_3521_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__6));
lean_inc_n(v___x_3516_, 2);
v___x_3522_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3522_, 0, v___x_3516_);
lean_ctor_set(v___x_3522_, 1, v___x_3518_);
lean_ctor_set(v___x_3522_, 2, v___x_3520_);
lean_ctor_set(v___x_3522_, 3, v___x_3521_);
v___x_3523_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_3524_ = l_Lean_Syntax_node2(v___x_3516_, v___x_3523_, v_a_3505_, v___x_3514_);
v___x_3525_ = l_Lean_Syntax_node2(v___x_3516_, v___x_3517_, v___x_3522_, v___x_3524_);
if (v_isShared_3509_ == 0)
{
lean_ctor_set(v___x_3508_, 0, v___x_3525_);
v___x_3527_ = v___x_3508_;
goto v_reusejp_3526_;
}
else
{
lean_object* v_reuseFailAlloc_3528_; 
v_reuseFailAlloc_3528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3528_, 0, v___x_3525_);
lean_ctor_set(v_reuseFailAlloc_3528_, 1, v_a_3506_);
v___x_3527_ = v_reuseFailAlloc_3528_;
goto v_reusejp_3526_;
}
v_reusejp_3526_:
{
return v___x_3527_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termZoned_x28___x2c___x29__1___boxed(lean_object* v_x_3530_, lean_object* v_a_3531_, lean_object* v_a_3532_){
_start:
{
lean_object* v_res_3533_; 
v_res_3533_ = l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termZoned_x28___x2c___x29__1(v_x_3530_, v_a_3531_, v_a_3532_);
lean_dec_ref(v_a_3531_);
return v_res_3533_;
}
}
LEAN_EXPORT lean_object* l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termDatetime_x28___x29__1(lean_object* v_x_3534_, lean_object* v_a_3535_, lean_object* v_a_3536_){
_start:
{
lean_object* v___x_3537_; uint8_t v___x_3538_; 
v___x_3537_ = ((lean_object*)(l_Std_Time_termDatetime_x28___x29___closed__1));
lean_inc(v_x_3534_);
v___x_3538_ = l_Lean_Syntax_isOfKind(v_x_3534_, v___x_3537_);
if (v___x_3538_ == 0)
{
lean_object* v___x_3539_; lean_object* v___x_3540_; 
lean_dec(v_x_3534_);
v___x_3539_ = lean_box(1);
v___x_3540_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3540_, 0, v___x_3539_);
lean_ctor_set(v___x_3540_, 1, v_a_3536_);
return v___x_3540_;
}
else
{
lean_object* v___x_3541_; lean_object* v_date_3542_; lean_object* v___x_3543_; uint8_t v___x_3544_; 
v___x_3541_ = lean_unsigned_to_nat(1u);
v_date_3542_ = l_Lean_Syntax_getArg(v_x_3534_, v___x_3541_);
lean_dec(v_x_3534_);
v___x_3543_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxString___closed__1));
lean_inc(v_date_3542_);
v___x_3544_ = l_Lean_Syntax_isOfKind(v_date_3542_, v___x_3543_);
if (v___x_3544_ == 0)
{
lean_object* v___x_3545_; lean_object* v___x_3546_; 
lean_dec(v_date_3542_);
v___x_3545_ = lean_box(1);
v___x_3546_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3546_, 0, v___x_3545_);
lean_ctor_set(v___x_3546_, 1, v_a_3536_);
return v___x_3546_;
}
else
{
lean_object* v___x_3547_; lean_object* v___x_3548_; 
v___x_3547_ = l_Lean_TSyntax_getString(v_date_3542_);
v___x_3548_ = l_Std_Time_PlainDateTime_fromLeanDateTimeString(v___x_3547_);
if (lean_obj_tag(v___x_3548_) == 0)
{
lean_object* v_a_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; 
v_a_3549_ = lean_ctor_get(v___x_3548_, 0);
lean_inc(v_a_3549_);
lean_dec_ref_known(v___x_3548_, 1);
v___x_3550_ = ((lean_object*)(l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termZoned_x28___x29__1___closed__0));
v___x_3551_ = lean_string_append(v___x_3550_, v_a_3549_);
lean_dec(v_a_3549_);
v___x_3552_ = l_Lean_Macro_throwErrorAt___redArg(v_date_3542_, v___x_3551_, v_a_3535_, v_a_3536_);
lean_dec(v_date_3542_);
return v___x_3552_;
}
else
{
lean_object* v_a_3553_; lean_object* v___x_3554_; lean_object* v_a_3555_; lean_object* v_a_3556_; lean_object* v___x_3558_; uint8_t v_isShared_3559_; uint8_t v_isSharedCheck_3563_; 
lean_dec(v_date_3542_);
v_a_3553_ = lean_ctor_get(v___x_3548_, 0);
lean_inc(v_a_3553_);
lean_dec_ref_known(v___x_3548_, 1);
v___x_3554_ = l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime(v_a_3553_, v_a_3535_, v_a_3536_);
v_a_3555_ = lean_ctor_get(v___x_3554_, 0);
v_a_3556_ = lean_ctor_get(v___x_3554_, 1);
v_isSharedCheck_3563_ = !lean_is_exclusive(v___x_3554_);
if (v_isSharedCheck_3563_ == 0)
{
v___x_3558_ = v___x_3554_;
v_isShared_3559_ = v_isSharedCheck_3563_;
goto v_resetjp_3557_;
}
else
{
lean_inc(v_a_3556_);
lean_inc(v_a_3555_);
lean_dec(v___x_3554_);
v___x_3558_ = lean_box(0);
v_isShared_3559_ = v_isSharedCheck_3563_;
goto v_resetjp_3557_;
}
v_resetjp_3557_:
{
lean_object* v___x_3561_; 
if (v_isShared_3559_ == 0)
{
v___x_3561_ = v___x_3558_;
goto v_reusejp_3560_;
}
else
{
lean_object* v_reuseFailAlloc_3562_; 
v_reuseFailAlloc_3562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3562_, 0, v_a_3555_);
lean_ctor_set(v_reuseFailAlloc_3562_, 1, v_a_3556_);
v___x_3561_ = v_reuseFailAlloc_3562_;
goto v_reusejp_3560_;
}
v_reusejp_3560_:
{
return v___x_3561_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termDatetime_x28___x29__1___boxed(lean_object* v_x_3564_, lean_object* v_a_3565_, lean_object* v_a_3566_){
_start:
{
lean_object* v_res_3567_; 
v_res_3567_ = l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termDatetime_x28___x29__1(v_x_3564_, v_a_3565_, v_a_3566_);
lean_dec_ref(v_a_3565_);
return v_res_3567_;
}
}
LEAN_EXPORT lean_object* l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termDate_x28___x29__1(lean_object* v_x_3568_, lean_object* v_a_3569_, lean_object* v_a_3570_){
_start:
{
lean_object* v___x_3571_; uint8_t v___x_3572_; 
v___x_3571_ = ((lean_object*)(l_Std_Time_termDate_x28___x29___closed__1));
lean_inc(v_x_3568_);
v___x_3572_ = l_Lean_Syntax_isOfKind(v_x_3568_, v___x_3571_);
if (v___x_3572_ == 0)
{
lean_object* v___x_3573_; lean_object* v___x_3574_; 
lean_dec(v_x_3568_);
v___x_3573_ = lean_box(1);
v___x_3574_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3574_, 0, v___x_3573_);
lean_ctor_set(v___x_3574_, 1, v_a_3570_);
return v___x_3574_;
}
else
{
lean_object* v___x_3575_; lean_object* v_date_3576_; lean_object* v___x_3577_; uint8_t v___x_3578_; 
v___x_3575_ = lean_unsigned_to_nat(1u);
v_date_3576_ = l_Lean_Syntax_getArg(v_x_3568_, v___x_3575_);
lean_dec(v_x_3568_);
v___x_3577_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxString___closed__1));
lean_inc(v_date_3576_);
v___x_3578_ = l_Lean_Syntax_isOfKind(v_date_3576_, v___x_3577_);
if (v___x_3578_ == 0)
{
lean_object* v___x_3579_; lean_object* v___x_3580_; 
lean_dec(v_date_3576_);
v___x_3579_ = lean_box(1);
v___x_3580_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3580_, 0, v___x_3579_);
lean_ctor_set(v___x_3580_, 1, v_a_3570_);
return v___x_3580_;
}
else
{
lean_object* v___x_3581_; lean_object* v___x_3582_; 
v___x_3581_ = l_Lean_TSyntax_getString(v_date_3576_);
v___x_3582_ = l_Std_Time_PlainDate_fromSQLDateString(v___x_3581_);
if (lean_obj_tag(v___x_3582_) == 0)
{
lean_object* v_a_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; 
v_a_3583_ = lean_ctor_get(v___x_3582_, 0);
lean_inc(v_a_3583_);
lean_dec_ref_known(v___x_3582_, 1);
v___x_3584_ = ((lean_object*)(l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termZoned_x28___x29__1___closed__0));
v___x_3585_ = lean_string_append(v___x_3584_, v_a_3583_);
lean_dec(v_a_3583_);
v___x_3586_ = l_Lean_Macro_throwErrorAt___redArg(v_date_3576_, v___x_3585_, v_a_3569_, v_a_3570_);
lean_dec(v_date_3576_);
return v___x_3586_;
}
else
{
lean_object* v_a_3587_; lean_object* v___x_3588_; lean_object* v_a_3589_; lean_object* v_a_3590_; lean_object* v___x_3592_; uint8_t v_isShared_3593_; uint8_t v_isSharedCheck_3597_; 
lean_dec(v_date_3576_);
v_a_3587_ = lean_ctor_get(v___x_3582_, 0);
lean_inc(v_a_3587_);
lean_dec_ref_known(v___x_3582_, 1);
v___x_3588_ = l___private_Std_Time_Notation_0__Std_Time_convertPlainDate(v_a_3587_, v_a_3569_, v_a_3570_);
lean_dec(v_a_3587_);
v_a_3589_ = lean_ctor_get(v___x_3588_, 0);
v_a_3590_ = lean_ctor_get(v___x_3588_, 1);
v_isSharedCheck_3597_ = !lean_is_exclusive(v___x_3588_);
if (v_isSharedCheck_3597_ == 0)
{
v___x_3592_ = v___x_3588_;
v_isShared_3593_ = v_isSharedCheck_3597_;
goto v_resetjp_3591_;
}
else
{
lean_inc(v_a_3590_);
lean_inc(v_a_3589_);
lean_dec(v___x_3588_);
v___x_3592_ = lean_box(0);
v_isShared_3593_ = v_isSharedCheck_3597_;
goto v_resetjp_3591_;
}
v_resetjp_3591_:
{
lean_object* v___x_3595_; 
if (v_isShared_3593_ == 0)
{
v___x_3595_ = v___x_3592_;
goto v_reusejp_3594_;
}
else
{
lean_object* v_reuseFailAlloc_3596_; 
v_reuseFailAlloc_3596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3596_, 0, v_a_3589_);
lean_ctor_set(v_reuseFailAlloc_3596_, 1, v_a_3590_);
v___x_3595_ = v_reuseFailAlloc_3596_;
goto v_reusejp_3594_;
}
v_reusejp_3594_:
{
return v___x_3595_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termDate_x28___x29__1___boxed(lean_object* v_x_3598_, lean_object* v_a_3599_, lean_object* v_a_3600_){
_start:
{
lean_object* v_res_3601_; 
v_res_3601_ = l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termDate_x28___x29__1(v_x_3598_, v_a_3599_, v_a_3600_);
lean_dec_ref(v_a_3599_);
return v_res_3601_;
}
}
LEAN_EXPORT lean_object* l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termTime_x28___x29__1(lean_object* v_x_3602_, lean_object* v_a_3603_, lean_object* v_a_3604_){
_start:
{
lean_object* v___x_3605_; uint8_t v___x_3606_; 
v___x_3605_ = ((lean_object*)(l_Std_Time_termTime_x28___x29___closed__1));
lean_inc(v_x_3602_);
v___x_3606_ = l_Lean_Syntax_isOfKind(v_x_3602_, v___x_3605_);
if (v___x_3606_ == 0)
{
lean_object* v___x_3607_; lean_object* v___x_3608_; 
lean_dec(v_x_3602_);
v___x_3607_ = lean_box(1);
v___x_3608_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3608_, 0, v___x_3607_);
lean_ctor_set(v___x_3608_, 1, v_a_3604_);
return v___x_3608_;
}
else
{
lean_object* v___x_3609_; lean_object* v_time_3610_; lean_object* v___x_3611_; uint8_t v___x_3612_; 
v___x_3609_ = lean_unsigned_to_nat(1u);
v_time_3610_ = l_Lean_Syntax_getArg(v_x_3602_, v___x_3609_);
lean_dec(v_x_3602_);
v___x_3611_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxString___closed__1));
lean_inc(v_time_3610_);
v___x_3612_ = l_Lean_Syntax_isOfKind(v_time_3610_, v___x_3611_);
if (v___x_3612_ == 0)
{
lean_object* v___x_3613_; lean_object* v___x_3614_; 
lean_dec(v_time_3610_);
v___x_3613_ = lean_box(1);
v___x_3614_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3614_, 0, v___x_3613_);
lean_ctor_set(v___x_3614_, 1, v_a_3604_);
return v___x_3614_;
}
else
{
lean_object* v___x_3615_; lean_object* v___x_3616_; 
v___x_3615_ = l_Lean_TSyntax_getString(v_time_3610_);
v___x_3616_ = l_Std_Time_PlainTime_fromLeanTime24Hour(v___x_3615_);
if (lean_obj_tag(v___x_3616_) == 0)
{
lean_object* v_a_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; 
v_a_3617_ = lean_ctor_get(v___x_3616_, 0);
lean_inc(v_a_3617_);
lean_dec_ref_known(v___x_3616_, 1);
v___x_3618_ = ((lean_object*)(l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termZoned_x28___x29__1___closed__0));
v___x_3619_ = lean_string_append(v___x_3618_, v_a_3617_);
lean_dec(v_a_3617_);
v___x_3620_ = l_Lean_Macro_throwErrorAt___redArg(v_time_3610_, v___x_3619_, v_a_3603_, v_a_3604_);
lean_dec(v_time_3610_);
return v___x_3620_;
}
else
{
lean_object* v_a_3621_; lean_object* v___x_3622_; lean_object* v_a_3623_; lean_object* v_a_3624_; lean_object* v___x_3626_; uint8_t v_isShared_3627_; uint8_t v_isSharedCheck_3631_; 
lean_dec(v_time_3610_);
v_a_3621_ = lean_ctor_get(v___x_3616_, 0);
lean_inc(v_a_3621_);
lean_dec_ref_known(v___x_3616_, 1);
v___x_3622_ = l___private_Std_Time_Notation_0__Std_Time_convertPlainTime(v_a_3621_, v_a_3603_, v_a_3604_);
v_a_3623_ = lean_ctor_get(v___x_3622_, 0);
v_a_3624_ = lean_ctor_get(v___x_3622_, 1);
v_isSharedCheck_3631_ = !lean_is_exclusive(v___x_3622_);
if (v_isSharedCheck_3631_ == 0)
{
v___x_3626_ = v___x_3622_;
v_isShared_3627_ = v_isSharedCheck_3631_;
goto v_resetjp_3625_;
}
else
{
lean_inc(v_a_3624_);
lean_inc(v_a_3623_);
lean_dec(v___x_3622_);
v___x_3626_ = lean_box(0);
v_isShared_3627_ = v_isSharedCheck_3631_;
goto v_resetjp_3625_;
}
v_resetjp_3625_:
{
lean_object* v___x_3629_; 
if (v_isShared_3627_ == 0)
{
v___x_3629_ = v___x_3626_;
goto v_reusejp_3628_;
}
else
{
lean_object* v_reuseFailAlloc_3630_; 
v_reuseFailAlloc_3630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3630_, 0, v_a_3623_);
lean_ctor_set(v_reuseFailAlloc_3630_, 1, v_a_3624_);
v___x_3629_ = v_reuseFailAlloc_3630_;
goto v_reusejp_3628_;
}
v_reusejp_3628_:
{
return v___x_3629_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termTime_x28___x29__1___boxed(lean_object* v_x_3632_, lean_object* v_a_3633_, lean_object* v_a_3634_){
_start:
{
lean_object* v_res_3635_; 
v_res_3635_ = l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termTime_x28___x29__1(v_x_3632_, v_a_3633_, v_a_3634_);
lean_dec_ref(v_a_3633_);
return v_res_3635_;
}
}
LEAN_EXPORT lean_object* l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termOffset_x28___x29__1(lean_object* v_x_3636_, lean_object* v_a_3637_, lean_object* v_a_3638_){
_start:
{
lean_object* v___x_3639_; uint8_t v___x_3640_; 
v___x_3639_ = ((lean_object*)(l_Std_Time_termOffset_x28___x29___closed__1));
lean_inc(v_x_3636_);
v___x_3640_ = l_Lean_Syntax_isOfKind(v_x_3636_, v___x_3639_);
if (v___x_3640_ == 0)
{
lean_object* v___x_3641_; lean_object* v___x_3642_; 
lean_dec(v_x_3636_);
v___x_3641_ = lean_box(1);
v___x_3642_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3642_, 0, v___x_3641_);
lean_ctor_set(v___x_3642_, 1, v_a_3638_);
return v___x_3642_;
}
else
{
lean_object* v___x_3643_; lean_object* v_offset_3644_; lean_object* v___x_3645_; uint8_t v___x_3646_; 
v___x_3643_ = lean_unsigned_to_nat(1u);
v_offset_3644_ = l_Lean_Syntax_getArg(v_x_3636_, v___x_3643_);
lean_dec(v_x_3636_);
v___x_3645_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxString___closed__1));
lean_inc(v_offset_3644_);
v___x_3646_ = l_Lean_Syntax_isOfKind(v_offset_3644_, v___x_3645_);
if (v___x_3646_ == 0)
{
lean_object* v___x_3647_; lean_object* v___x_3648_; 
lean_dec(v_offset_3644_);
v___x_3647_ = lean_box(1);
v___x_3648_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3648_, 0, v___x_3647_);
lean_ctor_set(v___x_3648_, 1, v_a_3638_);
return v___x_3648_;
}
else
{
lean_object* v___x_3649_; lean_object* v___x_3650_; 
v___x_3649_ = l_Lean_TSyntax_getString(v_offset_3644_);
v___x_3650_ = l_Std_Time_TimeZone_Offset_fromOffset(v___x_3649_);
if (lean_obj_tag(v___x_3650_) == 0)
{
lean_object* v_a_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; 
v_a_3651_ = lean_ctor_get(v___x_3650_, 0);
lean_inc(v_a_3651_);
lean_dec_ref_known(v___x_3650_, 1);
v___x_3652_ = ((lean_object*)(l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termZoned_x28___x29__1___closed__0));
v___x_3653_ = lean_string_append(v___x_3652_, v_a_3651_);
lean_dec(v_a_3651_);
v___x_3654_ = l_Lean_Macro_throwErrorAt___redArg(v_offset_3644_, v___x_3653_, v_a_3637_, v_a_3638_);
lean_dec(v_offset_3644_);
return v___x_3654_;
}
else
{
lean_object* v_a_3655_; lean_object* v___x_3656_; lean_object* v_a_3657_; lean_object* v_a_3658_; lean_object* v___x_3660_; uint8_t v_isShared_3661_; uint8_t v_isSharedCheck_3665_; 
lean_dec(v_offset_3644_);
v_a_3655_ = lean_ctor_get(v___x_3650_, 0);
lean_inc(v_a_3655_);
lean_dec_ref_known(v___x_3650_, 1);
v___x_3656_ = l___private_Std_Time_Notation_0__Std_Time_convertOffset(v_a_3655_, v_a_3637_, v_a_3638_);
lean_dec(v_a_3655_);
v_a_3657_ = lean_ctor_get(v___x_3656_, 0);
v_a_3658_ = lean_ctor_get(v___x_3656_, 1);
v_isSharedCheck_3665_ = !lean_is_exclusive(v___x_3656_);
if (v_isSharedCheck_3665_ == 0)
{
v___x_3660_ = v___x_3656_;
v_isShared_3661_ = v_isSharedCheck_3665_;
goto v_resetjp_3659_;
}
else
{
lean_inc(v_a_3658_);
lean_inc(v_a_3657_);
lean_dec(v___x_3656_);
v___x_3660_ = lean_box(0);
v_isShared_3661_ = v_isSharedCheck_3665_;
goto v_resetjp_3659_;
}
v_resetjp_3659_:
{
lean_object* v___x_3663_; 
if (v_isShared_3661_ == 0)
{
v___x_3663_ = v___x_3660_;
goto v_reusejp_3662_;
}
else
{
lean_object* v_reuseFailAlloc_3664_; 
v_reuseFailAlloc_3664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3664_, 0, v_a_3657_);
lean_ctor_set(v_reuseFailAlloc_3664_, 1, v_a_3658_);
v___x_3663_ = v_reuseFailAlloc_3664_;
goto v_reusejp_3662_;
}
v_reusejp_3662_:
{
return v___x_3663_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termOffset_x28___x29__1___boxed(lean_object* v_x_3666_, lean_object* v_a_3667_, lean_object* v_a_3668_){
_start:
{
lean_object* v_res_3669_; 
v_res_3669_ = l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termOffset_x28___x29__1(v_x_3666_, v_a_3667_, v_a_3668_);
lean_dec_ref(v_a_3667_);
return v_res_3669_;
}
}
LEAN_EXPORT lean_object* l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termTimezone_x28___x29__1(lean_object* v_x_3670_, lean_object* v_a_3671_, lean_object* v_a_3672_){
_start:
{
lean_object* v___x_3673_; uint8_t v___x_3674_; 
v___x_3673_ = ((lean_object*)(l_Std_Time_termTimezone_x28___x29___closed__1));
lean_inc(v_x_3670_);
v___x_3674_ = l_Lean_Syntax_isOfKind(v_x_3670_, v___x_3673_);
if (v___x_3674_ == 0)
{
lean_object* v___x_3675_; lean_object* v___x_3676_; 
lean_dec(v_x_3670_);
v___x_3675_ = lean_box(1);
v___x_3676_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3676_, 0, v___x_3675_);
lean_ctor_set(v___x_3676_, 1, v_a_3672_);
return v___x_3676_;
}
else
{
lean_object* v___x_3677_; lean_object* v_tz_3678_; lean_object* v___x_3679_; uint8_t v___x_3680_; 
v___x_3677_ = lean_unsigned_to_nat(1u);
v_tz_3678_ = l_Lean_Syntax_getArg(v_x_3670_, v___x_3677_);
lean_dec(v_x_3670_);
v___x_3679_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxString___closed__1));
lean_inc(v_tz_3678_);
v___x_3680_ = l_Lean_Syntax_isOfKind(v_tz_3678_, v___x_3679_);
if (v___x_3680_ == 0)
{
lean_object* v___x_3681_; lean_object* v___x_3682_; 
lean_dec(v_tz_3678_);
v___x_3681_ = lean_box(1);
v___x_3682_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3682_, 0, v___x_3681_);
lean_ctor_set(v___x_3682_, 1, v_a_3672_);
return v___x_3682_;
}
else
{
lean_object* v___x_3683_; lean_object* v___x_3684_; 
v___x_3683_ = l_Lean_TSyntax_getString(v_tz_3678_);
v___x_3684_ = l_Std_Time_TimeZone_fromTimeZone(v___x_3683_);
if (lean_obj_tag(v___x_3684_) == 0)
{
lean_object* v_a_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; 
v_a_3685_ = lean_ctor_get(v___x_3684_, 0);
lean_inc(v_a_3685_);
lean_dec_ref_known(v___x_3684_, 1);
v___x_3686_ = ((lean_object*)(l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termZoned_x28___x29__1___closed__0));
v___x_3687_ = lean_string_append(v___x_3686_, v_a_3685_);
lean_dec(v_a_3685_);
v___x_3688_ = l_Lean_Macro_throwErrorAt___redArg(v_tz_3678_, v___x_3687_, v_a_3671_, v_a_3672_);
lean_dec(v_tz_3678_);
return v___x_3688_;
}
else
{
lean_object* v_a_3689_; lean_object* v___x_3690_; lean_object* v_a_3691_; lean_object* v_a_3692_; lean_object* v___x_3694_; uint8_t v_isShared_3695_; uint8_t v_isSharedCheck_3699_; 
lean_dec(v_tz_3678_);
v_a_3689_ = lean_ctor_get(v___x_3684_, 0);
lean_inc(v_a_3689_);
lean_dec_ref_known(v___x_3684_, 1);
v___x_3690_ = l___private_Std_Time_Notation_0__Std_Time_convertTimezone(v_a_3689_, v_a_3671_, v_a_3672_);
v_a_3691_ = lean_ctor_get(v___x_3690_, 0);
v_a_3692_ = lean_ctor_get(v___x_3690_, 1);
v_isSharedCheck_3699_ = !lean_is_exclusive(v___x_3690_);
if (v_isSharedCheck_3699_ == 0)
{
v___x_3694_ = v___x_3690_;
v_isShared_3695_ = v_isSharedCheck_3699_;
goto v_resetjp_3693_;
}
else
{
lean_inc(v_a_3692_);
lean_inc(v_a_3691_);
lean_dec(v___x_3690_);
v___x_3694_ = lean_box(0);
v_isShared_3695_ = v_isSharedCheck_3699_;
goto v_resetjp_3693_;
}
v_resetjp_3693_:
{
lean_object* v___x_3697_; 
if (v_isShared_3695_ == 0)
{
v___x_3697_ = v___x_3694_;
goto v_reusejp_3696_;
}
else
{
lean_object* v_reuseFailAlloc_3698_; 
v_reuseFailAlloc_3698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3698_, 0, v_a_3691_);
lean_ctor_set(v_reuseFailAlloc_3698_, 1, v_a_3692_);
v___x_3697_ = v_reuseFailAlloc_3698_;
goto v_reusejp_3696_;
}
v_reusejp_3696_:
{
return v___x_3697_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termTimezone_x28___x29__1___boxed(lean_object* v_x_3700_, lean_object* v_a_3701_, lean_object* v_a_3702_){
_start:
{
lean_object* v_res_3703_; 
v_res_3703_ = l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termTimezone_x28___x29__1(v_x_3700_, v_a_3701_, v_a_3702_);
lean_dec_ref(v_a_3701_);
return v_res_3703_;
}
}
lean_object* runtime_initialize_Std_Time_Format(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Time_Notation(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Time_Format(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Std_Time_Format(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Time_Notation(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Std_Time_Format(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Time_Format(uint8_t builtin);
lean_object* initialize_Std_Time_Format(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Time_Notation(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time_Format(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_Format(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Notation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Time_Notation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Time_Notation(builtin);
}
#ifdef __cplusplus
}
#endif

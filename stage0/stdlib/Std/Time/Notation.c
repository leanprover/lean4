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
lean_object* l_Array_mkArray0___redArg();
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
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertText___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Std.Time.Text.twoLetterShort"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertText___closed__27 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__27_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertText___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertText___closed__28;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertText___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "twoLetterShort"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertText___closed__29 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__29_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertText___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertText___closed__30_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__30_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertText___closed__30_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__30_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__4_value),LEAN_SCALAR_PTR_LITERAL(173, 214, 90, 117, 56, 8, 198, 188)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertText___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__30_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__29_value),LEAN_SCALAR_PTR_LITERAL(168, 63, 137, 16, 74, 20, 200, 159)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertText___closed__30 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__30_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertText___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__30_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertText___closed__31 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__31_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertText___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__30_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertText___closed__32 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__32_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertText___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__32_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertText___closed__33 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__33_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertText___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__31_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__33_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertText___closed__34 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__34_value;
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
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Std.Time.ZoneId.unknown"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__0 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__0_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__1;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ZoneId"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__2 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__2_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "unknown"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__3 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__3_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__4_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__4_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__2_value),LEAN_SCALAR_PTR_LITERAL(15, 155, 217, 32, 218, 79, 133, 226)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__4_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__3_value),LEAN_SCALAR_PTR_LITERAL(81, 61, 96, 224, 240, 156, 239, 4)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__4 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__4_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__5 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__5_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__4_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__6 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__6_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__7 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__7_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__5_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__7_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__8 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__8_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Std.Time.ZoneId.short"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__9 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__9_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__10;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__11_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__11_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__2_value),LEAN_SCALAR_PTR_LITERAL(15, 155, 217, 32, 218, 79, 133, 226)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__11_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__5_value),LEAN_SCALAR_PTR_LITERAL(208, 236, 57, 76, 90, 0, 9, 31)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__11 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__11_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__11_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__12 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__12_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__11_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__13 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__13_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__13_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__14 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__14_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__12_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__14_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__15 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__15_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Std.Time.ZoneId.full"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__16 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__16_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__17;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__18_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__18_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__2_value),LEAN_SCALAR_PTR_LITERAL(15, 155, 217, 32, 218, 79, 133, 226)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__18_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__13_value),LEAN_SCALAR_PTR_LITERAL(67, 92, 171, 27, 57, 53, 132, 168)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__18 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__18_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__18_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__19 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__19_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__18_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__20 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__20_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__20_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__21 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__21_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__19_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__21_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__22 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__22_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZoneId(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZoneId___boxed(lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.u"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__9 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__9_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__10;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "u"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__11 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__11_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__12_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__12_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__12_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__11_value),LEAN_SCALAR_PTR_LITERAL(147, 80, 165, 32, 82, 240, 32, 222)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__12 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__12_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__12_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__13 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__13_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__12_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__14 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__14_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__14_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__15 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__15_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__13_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__15_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__16 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__16_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.y"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__17 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__17_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__18;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "y"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__19 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__19_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__20_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__20_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__20_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__19_value),LEAN_SCALAR_PTR_LITERAL(115, 95, 28, 131, 21, 96, 16, 178)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__20 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__20_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__20_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__21 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__21_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__20_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__22 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__22_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__22_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__23 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__23_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__21_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__23_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__24 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__24_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.D"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__25 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__25_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__26;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "D"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__27 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__27_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__28_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__28_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__28_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__28_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__28_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__27_value),LEAN_SCALAR_PTR_LITERAL(110, 212, 173, 37, 208, 12, 21, 131)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__28 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__28_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__28_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__29 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__29_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__28_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__30 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__30_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__30_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__31 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__31_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__29_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__31_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__32 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__32_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.M"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__33 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__33_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__34;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "M"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__35 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__35_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__36_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__36_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__36_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__36_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__36_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__36_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__35_value),LEAN_SCALAR_PTR_LITERAL(176, 179, 166, 105, 244, 184, 142, 60)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__36 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__36_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__36_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__37 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__37_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__36_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__38 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__38_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__38_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__39 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__39_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__37_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__39_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__40 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__40_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__41 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__41_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__42_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__42_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__42_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__42_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__42_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__42_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__41_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__42 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__42_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__43 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__43_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__44_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__44_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__44_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__44_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__44_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__44_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__43_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__44 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__44_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__45 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__45_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__46 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__46_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__46_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__47 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__47_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__48 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__48_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__50_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__50_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__50 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__50_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__50_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__51 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__51_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__52 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__52_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__52_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__53 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__53_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__54 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__54_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__55_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__55_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__55_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__55_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__54_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__55 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__55_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__55_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__56 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__56_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__57_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__57_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__57 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__57_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__57_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__58 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__58_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__59 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__59_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__59_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__60 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__60_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__60_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__61 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__61_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__58_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__61_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__62 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__62_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__56_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__62_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__63 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__63_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__53_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__63_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__64 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__64_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__51_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__64_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__65 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__65_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "dotIdent"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__66 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__66_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__67_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__67_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__67_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__67_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__67_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__67_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__66_value),LEAN_SCALAR_PTR_LITERAL(173, 139, 76, 218, 89, 59, 213, 196)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__67 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__67_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__68 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__68_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "inl"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__69 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__69_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__70_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__70;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__69_value),LEAN_SCALAR_PTR_LITERAL(86, 142, 99, 99, 156, 120, 56, 132)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__71 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__71_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__72 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__72_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "inr"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__73 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__73_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__74_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__74;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__73_value),LEAN_SCALAR_PTR_LITERAL(209, 212, 202, 104, 137, 8, 49, 108)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__75 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__75_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.L"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__76 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__76_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__77_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__77;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__78_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "L"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__78 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__78_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__79_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__79_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__79_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__79_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__79_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__79_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__78_value),LEAN_SCALAR_PTR_LITERAL(10, 49, 255, 3, 30, 59, 119, 162)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__79 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__79_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__80_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__79_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__80 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__80_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__81_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__79_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__81 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__81_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__82_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__81_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__82 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__82_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__83_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__80_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__82_value)}};
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
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__92_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.Q"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__92 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__92_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__93_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__93;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__94_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "Q"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__94 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__94_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__95_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__95_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__95_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__95_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__95_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__95_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__95_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__94_value),LEAN_SCALAR_PTR_LITERAL(2, 45, 222, 148, 85, 12, 195, 87)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__95 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__95_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__96_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__95_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__96 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__96_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__97_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__95_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__97 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__97_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__98_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__97_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__98 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__98_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__99_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__96_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__98_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__99 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__99_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__100_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.q"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__100 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__100_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__101_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__101;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__102_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "q"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__102 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__102_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__103_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__103_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__103_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__103_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__103_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__103_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__103_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__102_value),LEAN_SCALAR_PTR_LITERAL(236, 248, 36, 9, 92, 215, 91, 102)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__103 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__103_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__104_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__103_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__104 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__104_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__105_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__103_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__105 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__105_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__106_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__105_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__106 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__106_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__107_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__104_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__106_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__107 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__107_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__108_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.Y"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__108 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__108_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__109_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__109;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__110_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "Y"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__110 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__110_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__111_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__111_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__111_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__111_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__111_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__111_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__111_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__110_value),LEAN_SCALAR_PTR_LITERAL(14, 155, 135, 75, 42, 253, 153, 241)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__111 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__111_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__112_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__111_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__112 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__112_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__113_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__111_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__113 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__113_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__114_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__113_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__114 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__114_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__115_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__112_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__114_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__115 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__115_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__116_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.w"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__116 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__116_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__117_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__117;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__118_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "w"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__118 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__118_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__119_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__119_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__119_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__119_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__119_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__119_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__119_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__118_value),LEAN_SCALAR_PTR_LITERAL(109, 122, 115, 3, 58, 174, 210, 61)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__119 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__119_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__120_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__119_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__120 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__120_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__121_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__119_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__121 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__121_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__122_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__121_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__122 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__122_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__123_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__120_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__122_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__123 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__123_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__124_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.W"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__124 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__124_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__125_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__125;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__126_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "W"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__126 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__126_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__127_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__127_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__127_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__127_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__127_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__127_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__127_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__126_value),LEAN_SCALAR_PTR_LITERAL(142, 210, 249, 219, 201, 68, 141, 242)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__127 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__127_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__128_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__127_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__128 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__128_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__129_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__127_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__129 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__129_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__130_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__129_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__130 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__130_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__131_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__128_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__130_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__131 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__131_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__132_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.E"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__132 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__132_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__133_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__133;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__134_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "E"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__134 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__134_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__135_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__135_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__135_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__135_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__135_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__135_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__135_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__134_value),LEAN_SCALAR_PTR_LITERAL(221, 114, 205, 107, 57, 101, 237, 55)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__135 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__135_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__136_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__135_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__136 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__136_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__137_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__135_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__137 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__137_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__138_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__137_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__138 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__138_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__139_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__136_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__138_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__139 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__139_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__140_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.e"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__140 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__140_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__141_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__141;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__142_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "e"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__142 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__142_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__143_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__143_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__143_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__143_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__143_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__143_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__143_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__142_value),LEAN_SCALAR_PTR_LITERAL(65, 97, 136, 164, 196, 185, 6, 236)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__143 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__143_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__144_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__143_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__144 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__144_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__145_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__143_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__145 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__145_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__146_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__145_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__146 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__146_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__147_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__144_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__146_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__147 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__147_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__148_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.c"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__148 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__148_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__149_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__149;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__150_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "c"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__150 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__150_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__151_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__151_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__151_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__151_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__151_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__151_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__151_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__150_value),LEAN_SCALAR_PTR_LITERAL(85, 172, 192, 170, 145, 101, 192, 197)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__151 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__151_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__152_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__151_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__152 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__152_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__153_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__151_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__153 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__153_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__154_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__153_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__154 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__154_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__155_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__152_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__154_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__155 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__155_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__156_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.F"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__156 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__156_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__157_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__157;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__158_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "F"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__158 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__158_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__159_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__159_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__159_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__159_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__159_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__159_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__159_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__158_value),LEAN_SCALAR_PTR_LITERAL(255, 172, 252, 76, 184, 53, 176, 25)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__159 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__159_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__160_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__159_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__160 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__160_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__161_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__159_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__161 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__161_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__162_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__161_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__162 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__162_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__163_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__160_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__162_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__163 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__163_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__164_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.a"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__164 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__164_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__165_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__165;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__166_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "a"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__166 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__166_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__167_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__167_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__167_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__167_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__167_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__167_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__167_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__166_value),LEAN_SCALAR_PTR_LITERAL(36, 69, 244, 234, 150, 73, 242, 198)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__167 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__167_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__168_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__167_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__168 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__168_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__169_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__167_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__169 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__169_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__170_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__169_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__170 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__170_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__171_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__168_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__170_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__171 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__171_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__172_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.b"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__172 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__172_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__173_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__173;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__174_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "b"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__174 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__174_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__175_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__175_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__175_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__175_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__175_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__175_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__175_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__174_value),LEAN_SCALAR_PTR_LITERAL(44, 133, 176, 52, 47, 30, 166, 26)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__175 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__175_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__176_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__175_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__176 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__176_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__177_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__175_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__177 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__177_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__178_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__177_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__178 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__178_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__179_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__176_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__178_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__179 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__179_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__180_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.B"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__180 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__180_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__181_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__181;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__182_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "B"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__182 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__182_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__183_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__183_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__183_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__183_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__183_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__183_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__183_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__182_value),LEAN_SCALAR_PTR_LITERAL(235, 206, 18, 37, 245, 139, 43, 135)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__183 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__183_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__184_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__183_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__184 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__184_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__185_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__183_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__185 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__185_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__186_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__185_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__186 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__186_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__187_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__184_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__186_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__187 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__187_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__188_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.h"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__188 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__188_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__189_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__189;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__190_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__190 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__190_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__191_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__191_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__191_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__191_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__191_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__191_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__191_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__190_value),LEAN_SCALAR_PTR_LITERAL(171, 19, 0, 95, 105, 8, 122, 135)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__191 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__191_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__192_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__191_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__192 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__192_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__193_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__191_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__193 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__193_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__194_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__193_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__194 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__194_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__195_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__192_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__194_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__195 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__195_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__196_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.K"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__196 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__196_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__197_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__197;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__198_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "K"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__198 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__198_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__199_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__199_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__199_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__199_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__199_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__199_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__199_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__198_value),LEAN_SCALAR_PTR_LITERAL(175, 237, 107, 230, 188, 207, 116, 239)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__199 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__199_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__200_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__199_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__200 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__200_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__201_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__199_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__201 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__201_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__202_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__201_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__202 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__202_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__203_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__200_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__202_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__203 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__203_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__204_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.k"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__204 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__204_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__205_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__205;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__206_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "k"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__206 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__206_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__207_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__207_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__207_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__207_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__207_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__207_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__207_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__206_value),LEAN_SCALAR_PTR_LITERAL(186, 55, 92, 94, 160, 8, 215, 223)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__207 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__207_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__208_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__207_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__208 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__208_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__209_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__207_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__209 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__209_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__210_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__209_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__210 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__210_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__211_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__208_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__210_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__211 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__211_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__212_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.H"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__212 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__212_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__213_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__213;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__214_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "H"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__214 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__214_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__215_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__215_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__215_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__215_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__215_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__215_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__215_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__214_value),LEAN_SCALAR_PTR_LITERAL(202, 31, 161, 0, 128, 16, 18, 169)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__215 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__215_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__216_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__215_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__216 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__216_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__217_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__215_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__217 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__217_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__218_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__217_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__218 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__218_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__219_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__216_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__218_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__219 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__219_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__220_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.m"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__220 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__220_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__221_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__221;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__222_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "m"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__222 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__222_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__223_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__223_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__223_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__223_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__223_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__223_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__223_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__222_value),LEAN_SCALAR_PTR_LITERAL(118, 254, 173, 99, 0, 222, 89, 33)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__223 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__223_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__224_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__223_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__224 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__224_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__225_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__223_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__225 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__225_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__226_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__225_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__226 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__226_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__227_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__224_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__226_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__227 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__227_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__228_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.s"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__228 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__228_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__229_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__229;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__230_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "s"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__230 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__230_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__231_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__231_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__231_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__231_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__231_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__231_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__231_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__230_value),LEAN_SCALAR_PTR_LITERAL(80, 170, 75, 145, 176, 122, 31, 111)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__231 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__231_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__232_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__231_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__232 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__232_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__233_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__231_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__233 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__233_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__234_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__233_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__234 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__234_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__235_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__232_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__234_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__235 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__235_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__236_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.S"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__236 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__236_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__237_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__237;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__238_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "S"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__238 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__238_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__239_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__239_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__239_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__239_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__239_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__239_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__239_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__238_value),LEAN_SCALAR_PTR_LITERAL(61, 110, 227, 5, 165, 49, 182, 207)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__239 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__239_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__240_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__239_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__240 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__240_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__241_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__239_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__241 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__241_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__242_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__241_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__242 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__242_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__243_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__240_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__242_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__243 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__243_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__244_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.A"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__244 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__244_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__245_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__245;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__246_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "A"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__246 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__246_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__247_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__247_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__247_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__247_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__247_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__247_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__247_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__246_value),LEAN_SCALAR_PTR_LITERAL(254, 42, 156, 100, 183, 179, 31, 180)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__247 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__247_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__248_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__247_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__248 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__248_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__249_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__247_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__249 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__249_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__250_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__249_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__250 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__250_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__251_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__248_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__250_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__251 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__251_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__252_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.n"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__252 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__252_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__253_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__253;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__254_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "n"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__254 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__254_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__255_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__255_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__255_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__255_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__255_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__255_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__255_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__254_value),LEAN_SCALAR_PTR_LITERAL(38, 78, 251, 143, 117, 169, 85, 233)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__255 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__255_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__256_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__255_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__256 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__256_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__257_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__255_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__257 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__257_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__258_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__257_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__258 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__258_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__259_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__256_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__258_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__259 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__259_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__260_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.N"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__260 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__260_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__261_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__261;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__262_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "N"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__262 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__262_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__263_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__263_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__263_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__263_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__263_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__263_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__263_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__262_value),LEAN_SCALAR_PTR_LITERAL(139, 9, 15, 62, 231, 211, 146, 60)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__263 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__263_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__264_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__263_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__264 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__264_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__265_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__263_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__265 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__265_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__266_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__265_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__266 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__266_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__267_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__264_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__266_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__267 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__267_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__268_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.V"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__268 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__268_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__269_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__269;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__270_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "V"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__270 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__270_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__271_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__271_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__271_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__271_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__271_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__271_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__271_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__270_value),LEAN_SCALAR_PTR_LITERAL(49, 190, 37, 135, 7, 5, 128, 4)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__271 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__271_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__272_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__271_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__272 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__272_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__273_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__271_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__273 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__273_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__274_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__273_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__274 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__274_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__275_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__272_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__274_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__275 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__275_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__276_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.z"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__276 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__276_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__277_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__277;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__278_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "z"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__278 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__278_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__279_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__279_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__279_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__279_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__279_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__279_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__279_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__278_value),LEAN_SCALAR_PTR_LITERAL(181, 218, 97, 100, 129, 163, 177, 227)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__279 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__279_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__280_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__279_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__280 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__280_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__281_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__279_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__281 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__281_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__282_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__281_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__282 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__282_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__283_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__280_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__282_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__283 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__283_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__284_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.v"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__284 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__284_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__285_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__285;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__286_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "v"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__286 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__286_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__287_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__287_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__287_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__287_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__287_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__287_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__287_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__286_value),LEAN_SCALAR_PTR_LITERAL(213, 204, 59, 153, 58, 232, 246, 39)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__287 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__287_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__288_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__287_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__288 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__288_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__289_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__287_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__289 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__289_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__290_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__289_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__290 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__290_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__291_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__288_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__290_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__291 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__291_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__292_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.O"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__292 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__292_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__293_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__293;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__294_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "O"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__294 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__294_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__295_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__295_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__295_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__295_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__295_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__295_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__295_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__294_value),LEAN_SCALAR_PTR_LITERAL(58, 151, 205, 45, 234, 213, 167, 33)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__295 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__295_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__296_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__295_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__296 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__296_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__297_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__295_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__297 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__297_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__298_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__297_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__298 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__298_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__299_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__296_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__298_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__299 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__299_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__300_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.X"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__300 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__300_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__301_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__301;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__302_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "X"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__302 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__302_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__303_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__303_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__303_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__303_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__303_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__303_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__303_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__302_value),LEAN_SCALAR_PTR_LITERAL(26, 41, 196, 142, 13, 161, 206, 121)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__303 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__303_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__304_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__303_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__304 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__304_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__305_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__303_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__305 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__305_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__306_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__305_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__306 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__306_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__307_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__304_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__306_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__307 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__307_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__308_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.x"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__308 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__308_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__309_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__309;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__310_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__310 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__310_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__311_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__311_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__311_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__311_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__311_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__311_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__311_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__310_value),LEAN_SCALAR_PTR_LITERAL(200, 2, 62, 177, 15, 17, 219, 69)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__311 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__311_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__312_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__311_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__312 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__312_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__313_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__311_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__313 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__313_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__314_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__313_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__314 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__314_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__315_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__312_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__314_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__315 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__315_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__316_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.Z"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__316 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__316_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__317_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__317;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__318_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "Z"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__318 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__318_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__319_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__319_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__319_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__319_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__319_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__319_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__319_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__318_value),LEAN_SCALAR_PTR_LITERAL(44, 18, 171, 9, 22, 243, 82, 66)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__319 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__319_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__320_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__319_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__320 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__320_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__321_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__319_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__321 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__321_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__322_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__321_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__322 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__322_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__323_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__320_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__322_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__323 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__323_value;
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
static const lean_ctor_object l_Std_Time_termZoned_x28___x29___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__72_value)}};
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
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertText___closed__28(void){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_65_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertText___closed__27));
v___x_66_ = l_String_toRawSubstring_x27(v___x_65_);
return v___x_66_;
}
}
lean_object* l___private_Std_Time_Notation_0__Std_Time_convertText(uint8_t v_x_84_, lean_object* v_a_85_, lean_object* v_a_86_){
_start:
{
switch(v_x_84_)
{
case 0:
{
lean_object* v_quotContext_87_; lean_object* v_currMacroScope_88_; lean_object* v_ref_89_; uint8_t v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v_quotContext_87_ = lean_ctor_get(v_a_85_, 1);
v_currMacroScope_88_ = lean_ctor_get(v_a_85_, 2);
v_ref_89_ = lean_ctor_get(v_a_85_, 5);
v___x_90_ = 0;
v___x_91_ = l_Lean_SourceInfo_fromRef(v_ref_89_, v___x_90_);
v___x_92_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__1, &l___private_Std_Time_Notation_0__Std_Time_convertText___closed__1_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertText___closed__1);
v___x_93_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertText___closed__6));
lean_inc(v_currMacroScope_88_);
lean_inc(v_quotContext_87_);
v___x_94_ = l_Lean_addMacroScope(v_quotContext_87_, v___x_93_, v_currMacroScope_88_);
v___x_95_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertText___closed__10));
v___x_96_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_96_, 0, v___x_91_);
lean_ctor_set(v___x_96_, 1, v___x_92_);
lean_ctor_set(v___x_96_, 2, v___x_94_);
lean_ctor_set(v___x_96_, 3, v___x_95_);
v___x_97_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_97_, 0, v___x_96_);
lean_ctor_set(v___x_97_, 1, v_a_86_);
return v___x_97_;
}
case 1:
{
lean_object* v_quotContext_98_; lean_object* v_currMacroScope_99_; lean_object* v_ref_100_; uint8_t v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v_quotContext_98_ = lean_ctor_get(v_a_85_, 1);
v_currMacroScope_99_ = lean_ctor_get(v_a_85_, 2);
v_ref_100_ = lean_ctor_get(v_a_85_, 5);
v___x_101_ = 0;
v___x_102_ = l_Lean_SourceInfo_fromRef(v_ref_100_, v___x_101_);
v___x_103_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__12, &l___private_Std_Time_Notation_0__Std_Time_convertText___closed__12_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertText___closed__12);
v___x_104_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertText___closed__14));
lean_inc(v_currMacroScope_99_);
lean_inc(v_quotContext_98_);
v___x_105_ = l_Lean_addMacroScope(v_quotContext_98_, v___x_104_, v_currMacroScope_99_);
v___x_106_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertText___closed__18));
v___x_107_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_107_, 0, v___x_102_);
lean_ctor_set(v___x_107_, 1, v___x_103_);
lean_ctor_set(v___x_107_, 2, v___x_105_);
lean_ctor_set(v___x_107_, 3, v___x_106_);
v___x_108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_108_, 0, v___x_107_);
lean_ctor_set(v___x_108_, 1, v_a_86_);
return v___x_108_;
}
case 2:
{
lean_object* v_quotContext_109_; lean_object* v_currMacroScope_110_; lean_object* v_ref_111_; uint8_t v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v_quotContext_109_ = lean_ctor_get(v_a_85_, 1);
v_currMacroScope_110_ = lean_ctor_get(v_a_85_, 2);
v_ref_111_ = lean_ctor_get(v_a_85_, 5);
v___x_112_ = 0;
v___x_113_ = l_Lean_SourceInfo_fromRef(v_ref_111_, v___x_112_);
v___x_114_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__20, &l___private_Std_Time_Notation_0__Std_Time_convertText___closed__20_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertText___closed__20);
v___x_115_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertText___closed__22));
lean_inc(v_currMacroScope_110_);
lean_inc(v_quotContext_109_);
v___x_116_ = l_Lean_addMacroScope(v_quotContext_109_, v___x_115_, v_currMacroScope_110_);
v___x_117_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertText___closed__26));
v___x_118_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_118_, 0, v___x_113_);
lean_ctor_set(v___x_118_, 1, v___x_114_);
lean_ctor_set(v___x_118_, 2, v___x_116_);
lean_ctor_set(v___x_118_, 3, v___x_117_);
v___x_119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_119_, 0, v___x_118_);
lean_ctor_set(v___x_119_, 1, v_a_86_);
return v___x_119_;
}
default: 
{
lean_object* v_quotContext_120_; lean_object* v_currMacroScope_121_; lean_object* v_ref_122_; uint8_t v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v_quotContext_120_ = lean_ctor_get(v_a_85_, 1);
v_currMacroScope_121_ = lean_ctor_get(v_a_85_, 2);
v_ref_122_ = lean_ctor_get(v_a_85_, 5);
v___x_123_ = 0;
v___x_124_ = l_Lean_SourceInfo_fromRef(v_ref_122_, v___x_123_);
v___x_125_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__28, &l___private_Std_Time_Notation_0__Std_Time_convertText___closed__28_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertText___closed__28);
v___x_126_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertText___closed__30));
lean_inc(v_currMacroScope_121_);
lean_inc(v_quotContext_120_);
v___x_127_ = l_Lean_addMacroScope(v_quotContext_120_, v___x_126_, v_currMacroScope_121_);
v___x_128_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertText___closed__34));
v___x_129_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_129_, 0, v___x_124_);
lean_ctor_set(v___x_129_, 1, v___x_125_);
lean_ctor_set(v___x_129_, 2, v___x_127_);
lean_ctor_set(v___x_129_, 3, v___x_128_);
v___x_130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_130_, 0, v___x_129_);
lean_ctor_set(v___x_130_, 1, v_a_86_);
return v___x_130_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Time_Notation_0__Std_Time_convertText_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_84_ = stack[0].m_num;
lean_object* v_a_85_ = stack[1].m_obj;
lean_object* v_a_86_ = stack[2].m_obj;
lean_object* v_res_131_;
v_res_131_ = l___private_Std_Time_Notation_0__Std_Time_convertText(v_x_84_, v_a_85_, v_a_86_);
stack->m_obj
 = v_res_131_;
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertText___boxed(lean_object* v_x_132_, lean_object* v_a_133_, lean_object* v_a_134_){
_start:
{
uint8_t v_x_5295__boxed_135_; lean_object* v_res_136_; 
v_x_5295__boxed_135_ = lean_unbox(v_x_132_);
v_res_136_ = l___private_Std_Time_Notation_0__Std_Time_convertText(v_x_5295__boxed_135_, v_a_133_, v_a_134_);
lean_dec_ref(v_a_133_);
return v_res_136_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__6(void){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_147_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__5));
v___x_148_ = l_String_toRawSubstring_x27(v___x_147_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertNumber(lean_object* v_x_170_, lean_object* v_a_171_, lean_object* v_a_172_){
_start:
{
lean_object* v_quotContext_173_; lean_object* v_currMacroScope_174_; lean_object* v_ref_175_; uint8_t v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v_quotContext_173_ = lean_ctor_get(v_a_171_, 1);
v_currMacroScope_174_ = lean_ctor_get(v_a_171_, 2);
v_ref_175_ = lean_ctor_get(v_a_171_, 5);
v___x_176_ = 0;
v___x_177_ = l_Lean_SourceInfo_fromRef(v_ref_175_, v___x_176_);
v___x_178_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_179_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__6, &l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__6_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__6);
v___x_180_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__9));
lean_inc(v_currMacroScope_174_);
lean_inc(v_quotContext_173_);
v___x_181_ = l_Lean_addMacroScope(v_quotContext_173_, v___x_180_, v_currMacroScope_174_);
v___x_182_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__13));
lean_inc_n(v___x_177_, 2);
v___x_183_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_183_, 0, v___x_177_);
lean_ctor_set(v___x_183_, 1, v___x_179_);
lean_ctor_set(v___x_183_, 2, v___x_181_);
lean_ctor_set(v___x_183_, 3, v___x_182_);
v___x_184_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_185_ = l_Nat_reprFast(v_x_170_);
v___x_186_ = lean_box(2);
v___x_187_ = l_Lean_Syntax_mkNumLit(v___x_185_, v___x_186_);
v___x_188_ = l_Lean_Syntax_node1(v___x_177_, v___x_184_, v___x_187_);
v___x_189_ = l_Lean_Syntax_node2(v___x_177_, v___x_178_, v___x_183_, v___x_188_);
v___x_190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_190_, 0, v___x_189_);
lean_ctor_set(v___x_190_, 1, v_a_172_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertNumber___boxed(lean_object* v_x_191_, lean_object* v_a_192_, lean_object* v_a_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l___private_Std_Time_Notation_0__Std_Time_convertNumber(v_x_191_, v_a_192_, v_a_193_);
lean_dec_ref(v_a_192_);
return v_res_194_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__1(void){
_start:
{
lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_196_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__0));
v___x_197_ = l_String_toRawSubstring_x27(v___x_196_);
return v___x_197_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__10(void){
_start:
{
lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_217_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__9));
v___x_218_ = l_String_toRawSubstring_x27(v___x_217_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertFraction(lean_object* v_x_236_, lean_object* v_a_237_, lean_object* v_a_238_){
_start:
{
if (lean_obj_tag(v_x_236_) == 0)
{
lean_object* v_quotContext_239_; lean_object* v_currMacroScope_240_; lean_object* v_ref_241_; uint8_t v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v_quotContext_239_ = lean_ctor_get(v_a_237_, 1);
v_currMacroScope_240_ = lean_ctor_get(v_a_237_, 2);
v_ref_241_ = lean_ctor_get(v_a_237_, 5);
v___x_242_ = 0;
v___x_243_ = l_Lean_SourceInfo_fromRef(v_ref_241_, v___x_242_);
v___x_244_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__1, &l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__1_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__1);
v___x_245_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__4));
lean_inc(v_currMacroScope_240_);
lean_inc(v_quotContext_239_);
v___x_246_ = l_Lean_addMacroScope(v_quotContext_239_, v___x_245_, v_currMacroScope_240_);
v___x_247_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__8));
v___x_248_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_248_, 0, v___x_243_);
lean_ctor_set(v___x_248_, 1, v___x_244_);
lean_ctor_set(v___x_248_, 2, v___x_246_);
lean_ctor_set(v___x_248_, 3, v___x_247_);
v___x_249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_249_, 0, v___x_248_);
lean_ctor_set(v___x_249_, 1, v_a_238_);
return v___x_249_;
}
else
{
lean_object* v_digits_250_; lean_object* v_quotContext_251_; lean_object* v_currMacroScope_252_; lean_object* v_ref_253_; uint8_t v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v_digits_250_ = lean_ctor_get(v_x_236_, 0);
lean_inc(v_digits_250_);
lean_dec_ref_known(v_x_236_, 1);
v_quotContext_251_ = lean_ctor_get(v_a_237_, 1);
v_currMacroScope_252_ = lean_ctor_get(v_a_237_, 2);
v_ref_253_ = lean_ctor_get(v_a_237_, 5);
v___x_254_ = 0;
v___x_255_ = l_Lean_SourceInfo_fromRef(v_ref_253_, v___x_254_);
v___x_256_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_257_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__10, &l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__10_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__10);
v___x_258_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__12));
lean_inc(v_currMacroScope_252_);
lean_inc(v_quotContext_251_);
v___x_259_ = l_Lean_addMacroScope(v_quotContext_251_, v___x_258_, v_currMacroScope_252_);
v___x_260_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__16));
lean_inc_n(v___x_255_, 2);
v___x_261_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_261_, 0, v___x_255_);
lean_ctor_set(v___x_261_, 1, v___x_257_);
lean_ctor_set(v___x_261_, 2, v___x_259_);
lean_ctor_set(v___x_261_, 3, v___x_260_);
v___x_262_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_263_ = l_Nat_reprFast(v_digits_250_);
v___x_264_ = lean_box(2);
v___x_265_ = l_Lean_Syntax_mkNumLit(v___x_263_, v___x_264_);
v___x_266_ = l_Lean_Syntax_node1(v___x_255_, v___x_262_, v___x_265_);
v___x_267_ = l_Lean_Syntax_node2(v___x_255_, v___x_256_, v___x_261_, v___x_266_);
v___x_268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_268_, 0, v___x_267_);
lean_ctor_set(v___x_268_, 1, v_a_238_);
return v___x_268_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertFraction___boxed(lean_object* v_x_269_, lean_object* v_a_270_, lean_object* v_a_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l___private_Std_Time_Notation_0__Std_Time_convertFraction(v_x_269_, v_a_270_, v_a_271_);
lean_dec_ref(v_a_270_);
return v_res_272_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__1(void){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_274_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__0));
v___x_275_ = l_String_toRawSubstring_x27(v___x_274_);
return v___x_275_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__10(void){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_295_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__9));
v___x_296_ = l_String_toRawSubstring_x27(v___x_295_);
return v___x_296_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__18(void){
_start:
{
lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_315_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__17));
v___x_316_ = l_String_toRawSubstring_x27(v___x_315_);
return v___x_316_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__26(void){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_335_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__25));
v___x_336_ = l_String_toRawSubstring_x27(v___x_335_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertYear(lean_object* v_x_354_, lean_object* v_a_355_, lean_object* v_a_356_){
_start:
{
switch(lean_obj_tag(v_x_354_))
{
case 0:
{
lean_object* v_quotContext_357_; lean_object* v_currMacroScope_358_; lean_object* v_ref_359_; uint8_t v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
v_quotContext_357_ = lean_ctor_get(v_a_355_, 1);
v_currMacroScope_358_ = lean_ctor_get(v_a_355_, 2);
v_ref_359_ = lean_ctor_get(v_a_355_, 5);
v___x_360_ = 0;
v___x_361_ = l_Lean_SourceInfo_fromRef(v_ref_359_, v___x_360_);
v___x_362_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__1, &l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__1_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__1);
v___x_363_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__4));
lean_inc(v_currMacroScope_358_);
lean_inc(v_quotContext_357_);
v___x_364_ = l_Lean_addMacroScope(v_quotContext_357_, v___x_363_, v_currMacroScope_358_);
v___x_365_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__8));
v___x_366_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_366_, 0, v___x_361_);
lean_ctor_set(v___x_366_, 1, v___x_362_);
lean_ctor_set(v___x_366_, 2, v___x_364_);
lean_ctor_set(v___x_366_, 3, v___x_365_);
v___x_367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_367_, 0, v___x_366_);
lean_ctor_set(v___x_367_, 1, v_a_356_);
return v___x_367_;
}
case 1:
{
lean_object* v_quotContext_368_; lean_object* v_currMacroScope_369_; lean_object* v_ref_370_; uint8_t v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
v_quotContext_368_ = lean_ctor_get(v_a_355_, 1);
v_currMacroScope_369_ = lean_ctor_get(v_a_355_, 2);
v_ref_370_ = lean_ctor_get(v_a_355_, 5);
v___x_371_ = 0;
v___x_372_ = l_Lean_SourceInfo_fromRef(v_ref_370_, v___x_371_);
v___x_373_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__10, &l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__10_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__10);
v___x_374_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__12));
lean_inc(v_currMacroScope_369_);
lean_inc(v_quotContext_368_);
v___x_375_ = l_Lean_addMacroScope(v_quotContext_368_, v___x_374_, v_currMacroScope_369_);
v___x_376_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__16));
v___x_377_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_377_, 0, v___x_372_);
lean_ctor_set(v___x_377_, 1, v___x_373_);
lean_ctor_set(v___x_377_, 2, v___x_375_);
lean_ctor_set(v___x_377_, 3, v___x_376_);
v___x_378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_378_, 0, v___x_377_);
lean_ctor_set(v___x_378_, 1, v_a_356_);
return v___x_378_;
}
case 2:
{
lean_object* v_quotContext_379_; lean_object* v_currMacroScope_380_; lean_object* v_ref_381_; uint8_t v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
v_quotContext_379_ = lean_ctor_get(v_a_355_, 1);
v_currMacroScope_380_ = lean_ctor_get(v_a_355_, 2);
v_ref_381_ = lean_ctor_get(v_a_355_, 5);
v___x_382_ = 0;
v___x_383_ = l_Lean_SourceInfo_fromRef(v_ref_381_, v___x_382_);
v___x_384_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__18, &l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__18_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__18);
v___x_385_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__20));
lean_inc(v_currMacroScope_380_);
lean_inc(v_quotContext_379_);
v___x_386_ = l_Lean_addMacroScope(v_quotContext_379_, v___x_385_, v_currMacroScope_380_);
v___x_387_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__24));
v___x_388_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_388_, 0, v___x_383_);
lean_ctor_set(v___x_388_, 1, v___x_384_);
lean_ctor_set(v___x_388_, 2, v___x_386_);
lean_ctor_set(v___x_388_, 3, v___x_387_);
v___x_389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_389_, 0, v___x_388_);
lean_ctor_set(v___x_389_, 1, v_a_356_);
return v___x_389_;
}
default: 
{
lean_object* v_num_390_; lean_object* v_quotContext_391_; lean_object* v_currMacroScope_392_; lean_object* v_ref_393_; uint8_t v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v_num_390_ = lean_ctor_get(v_x_354_, 0);
lean_inc(v_num_390_);
lean_dec_ref_known(v_x_354_, 1);
v_quotContext_391_ = lean_ctor_get(v_a_355_, 1);
v_currMacroScope_392_ = lean_ctor_get(v_a_355_, 2);
v_ref_393_ = lean_ctor_get(v_a_355_, 5);
v___x_394_ = 0;
v___x_395_ = l_Lean_SourceInfo_fromRef(v_ref_393_, v___x_394_);
v___x_396_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_397_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__26, &l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__26_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__26);
v___x_398_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__28));
lean_inc(v_currMacroScope_392_);
lean_inc(v_quotContext_391_);
v___x_399_ = l_Lean_addMacroScope(v_quotContext_391_, v___x_398_, v_currMacroScope_392_);
v___x_400_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__32));
lean_inc_n(v___x_395_, 2);
v___x_401_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_401_, 0, v___x_395_);
lean_ctor_set(v___x_401_, 1, v___x_397_);
lean_ctor_set(v___x_401_, 2, v___x_399_);
lean_ctor_set(v___x_401_, 3, v___x_400_);
v___x_402_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_403_ = l_Nat_reprFast(v_num_390_);
v___x_404_ = lean_box(2);
v___x_405_ = l_Lean_Syntax_mkNumLit(v___x_403_, v___x_404_);
v___x_406_ = l_Lean_Syntax_node1(v___x_395_, v___x_402_, v___x_405_);
v___x_407_ = l_Lean_Syntax_node2(v___x_395_, v___x_396_, v___x_401_, v___x_406_);
v___x_408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_408_, 0, v___x_407_);
lean_ctor_set(v___x_408_, 1, v_a_356_);
return v___x_408_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertYear___boxed(lean_object* v_x_409_, lean_object* v_a_410_, lean_object* v_a_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l___private_Std_Time_Notation_0__Std_Time_convertYear(v_x_409_, v_a_410_, v_a_411_);
lean_dec_ref(v_a_410_);
return v_res_412_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__1(void){
_start:
{
lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_414_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__0));
v___x_415_ = l_String_toRawSubstring_x27(v___x_414_);
return v___x_415_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__10(void){
_start:
{
lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_435_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__9));
v___x_436_ = l_String_toRawSubstring_x27(v___x_435_);
return v___x_436_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__17(void){
_start:
{
lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_454_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__16));
v___x_455_ = l_String_toRawSubstring_x27(v___x_454_);
return v___x_455_;
}
}
lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZoneId(uint8_t v_x_472_, lean_object* v_a_473_, lean_object* v_a_474_){
_start:
{
switch(v_x_472_)
{
case 0:
{
lean_object* v_quotContext_475_; lean_object* v_currMacroScope_476_; lean_object* v_ref_477_; uint8_t v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; 
v_quotContext_475_ = lean_ctor_get(v_a_473_, 1);
v_currMacroScope_476_ = lean_ctor_get(v_a_473_, 2);
v_ref_477_ = lean_ctor_get(v_a_473_, 5);
v___x_478_ = 0;
v___x_479_ = l_Lean_SourceInfo_fromRef(v_ref_477_, v___x_478_);
v___x_480_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__1, &l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__1_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__1);
v___x_481_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__4));
lean_inc(v_currMacroScope_476_);
lean_inc(v_quotContext_475_);
v___x_482_ = l_Lean_addMacroScope(v_quotContext_475_, v___x_481_, v_currMacroScope_476_);
v___x_483_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__8));
v___x_484_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_484_, 0, v___x_479_);
lean_ctor_set(v___x_484_, 1, v___x_480_);
lean_ctor_set(v___x_484_, 2, v___x_482_);
lean_ctor_set(v___x_484_, 3, v___x_483_);
v___x_485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_485_, 0, v___x_484_);
lean_ctor_set(v___x_485_, 1, v_a_474_);
return v___x_485_;
}
case 1:
{
lean_object* v_quotContext_486_; lean_object* v_currMacroScope_487_; lean_object* v_ref_488_; uint8_t v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
v_quotContext_486_ = lean_ctor_get(v_a_473_, 1);
v_currMacroScope_487_ = lean_ctor_get(v_a_473_, 2);
v_ref_488_ = lean_ctor_get(v_a_473_, 5);
v___x_489_ = 0;
v___x_490_ = l_Lean_SourceInfo_fromRef(v_ref_488_, v___x_489_);
v___x_491_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__10, &l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__10_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__10);
v___x_492_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__11));
lean_inc(v_currMacroScope_487_);
lean_inc(v_quotContext_486_);
v___x_493_ = l_Lean_addMacroScope(v_quotContext_486_, v___x_492_, v_currMacroScope_487_);
v___x_494_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__15));
v___x_495_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_495_, 0, v___x_490_);
lean_ctor_set(v___x_495_, 1, v___x_491_);
lean_ctor_set(v___x_495_, 2, v___x_493_);
lean_ctor_set(v___x_495_, 3, v___x_494_);
v___x_496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_496_, 0, v___x_495_);
lean_ctor_set(v___x_496_, 1, v_a_474_);
return v___x_496_;
}
default: 
{
lean_object* v_quotContext_497_; lean_object* v_currMacroScope_498_; lean_object* v_ref_499_; uint8_t v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
v_quotContext_497_ = lean_ctor_get(v_a_473_, 1);
v_currMacroScope_498_ = lean_ctor_get(v_a_473_, 2);
v_ref_499_ = lean_ctor_get(v_a_473_, 5);
v___x_500_ = 0;
v___x_501_ = l_Lean_SourceInfo_fromRef(v_ref_499_, v___x_500_);
v___x_502_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__17, &l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__17_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__17);
v___x_503_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__18));
lean_inc(v_currMacroScope_498_);
lean_inc(v_quotContext_497_);
v___x_504_ = l_Lean_addMacroScope(v_quotContext_497_, v___x_503_, v_currMacroScope_498_);
v___x_505_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertZoneId___closed__22));
v___x_506_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_506_, 0, v___x_501_);
lean_ctor_set(v___x_506_, 1, v___x_502_);
lean_ctor_set(v___x_506_, 2, v___x_504_);
lean_ctor_set(v___x_506_, 3, v___x_505_);
v___x_507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_507_, 0, v___x_506_);
lean_ctor_set(v___x_507_, 1, v_a_474_);
return v___x_507_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Time_Notation_0__Std_Time_convertZoneId_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_472_ = stack[0].m_num;
lean_object* v_a_473_ = stack[1].m_obj;
lean_object* v_a_474_ = stack[2].m_obj;
lean_object* v_res_508_;
v_res_508_ = l___private_Std_Time_Notation_0__Std_Time_convertZoneId(v_x_472_, v_a_473_, v_a_474_);
stack->m_obj
 = v_res_508_;
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZoneId___boxed(lean_object* v_x_509_, lean_object* v_a_510_, lean_object* v_a_511_){
_start:
{
uint8_t v_x_3970__boxed_512_; lean_object* v_res_513_; 
v_x_3970__boxed_512_ = lean_unbox(v_x_509_);
v_res_513_ = l___private_Std_Time_Notation_0__Std_Time_convertZoneId(v_x_3970__boxed_512_, v_a_510_, v_a_511_);
lean_dec_ref(v_a_510_);
return v_res_513_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__1(void){
_start:
{
lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_515_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__0));
v___x_516_ = l_String_toRawSubstring_x27(v___x_515_);
return v___x_516_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__9(void){
_start:
{
lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_535_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__8));
v___x_536_ = l_String_toRawSubstring_x27(v___x_535_);
return v___x_536_;
}
}
lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZoneName(uint8_t v_x_553_, lean_object* v_a_554_, lean_object* v_a_555_){
_start:
{
if (v_x_553_ == 0)
{
lean_object* v_quotContext_556_; lean_object* v_currMacroScope_557_; lean_object* v_ref_558_; uint8_t v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
v_quotContext_556_ = lean_ctor_get(v_a_554_, 1);
v_currMacroScope_557_ = lean_ctor_get(v_a_554_, 2);
v_ref_558_ = lean_ctor_get(v_a_554_, 5);
v___x_559_ = 0;
v___x_560_ = l_Lean_SourceInfo_fromRef(v_ref_558_, v___x_559_);
v___x_561_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__1, &l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__1_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__1);
v___x_562_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__3));
lean_inc(v_currMacroScope_557_);
lean_inc(v_quotContext_556_);
v___x_563_ = l_Lean_addMacroScope(v_quotContext_556_, v___x_562_, v_currMacroScope_557_);
v___x_564_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__7));
v___x_565_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_565_, 0, v___x_560_);
lean_ctor_set(v___x_565_, 1, v___x_561_);
lean_ctor_set(v___x_565_, 2, v___x_563_);
lean_ctor_set(v___x_565_, 3, v___x_564_);
v___x_566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_566_, 0, v___x_565_);
lean_ctor_set(v___x_566_, 1, v_a_555_);
return v___x_566_;
}
else
{
lean_object* v_quotContext_567_; lean_object* v_currMacroScope_568_; lean_object* v_ref_569_; uint8_t v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
v_quotContext_567_ = lean_ctor_get(v_a_554_, 1);
v_currMacroScope_568_ = lean_ctor_get(v_a_554_, 2);
v_ref_569_ = lean_ctor_get(v_a_554_, 5);
v___x_570_ = 0;
v___x_571_ = l_Lean_SourceInfo_fromRef(v_ref_569_, v___x_570_);
v___x_572_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__9, &l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__9_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__9);
v___x_573_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__10));
lean_inc(v_currMacroScope_568_);
lean_inc(v_quotContext_567_);
v___x_574_ = l_Lean_addMacroScope(v_quotContext_567_, v___x_573_, v_currMacroScope_568_);
v___x_575_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__14));
v___x_576_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_576_, 0, v___x_571_);
lean_ctor_set(v___x_576_, 1, v___x_572_);
lean_ctor_set(v___x_576_, 2, v___x_574_);
lean_ctor_set(v___x_576_, 3, v___x_575_);
v___x_577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_577_, 0, v___x_576_);
lean_ctor_set(v___x_577_, 1, v_a_555_);
return v___x_577_;
}
}
}
LEAN_EXPORT void l___private_Std_Time_Notation_0__Std_Time_convertZoneName_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_553_ = stack[0].m_num;
lean_object* v_a_554_ = stack[1].m_obj;
lean_object* v_a_555_ = stack[2].m_obj;
lean_object* v_res_578_;
v_res_578_ = l___private_Std_Time_Notation_0__Std_Time_convertZoneName(v_x_553_, v_a_554_, v_a_555_);
stack->m_obj
 = v_res_578_;
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZoneName___boxed(lean_object* v_x_579_, lean_object* v_a_580_, lean_object* v_a_581_){
_start:
{
uint8_t v_x_2649__boxed_582_; lean_object* v_res_583_; 
v_x_2649__boxed_582_ = lean_unbox(v_x_579_);
v_res_583_ = l___private_Std_Time_Notation_0__Std_Time_convertZoneName(v_x_2649__boxed_582_, v_a_580_, v_a_581_);
lean_dec_ref(v_a_580_);
return v_res_583_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__1(void){
_start:
{
lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_585_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__0));
v___x_586_ = l_String_toRawSubstring_x27(v___x_585_);
return v___x_586_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__10(void){
_start:
{
lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_606_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__9));
v___x_607_ = l_String_toRawSubstring_x27(v___x_606_);
return v___x_607_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__18(void){
_start:
{
lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_626_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__17));
v___x_627_ = l_String_toRawSubstring_x27(v___x_626_);
return v___x_627_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__26(void){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_646_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__25));
v___x_647_ = l_String_toRawSubstring_x27(v___x_646_);
return v___x_647_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__34(void){
_start:
{
lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_666_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__33));
v___x_667_ = l_String_toRawSubstring_x27(v___x_666_);
return v___x_667_;
}
}
lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetX(uint8_t v_x_685_, lean_object* v_a_686_, lean_object* v_a_687_){
_start:
{
switch(v_x_685_)
{
case 0:
{
lean_object* v_quotContext_688_; lean_object* v_currMacroScope_689_; lean_object* v_ref_690_; uint8_t v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
v_quotContext_688_ = lean_ctor_get(v_a_686_, 1);
v_currMacroScope_689_ = lean_ctor_get(v_a_686_, 2);
v_ref_690_ = lean_ctor_get(v_a_686_, 5);
v___x_691_ = 0;
v___x_692_ = l_Lean_SourceInfo_fromRef(v_ref_690_, v___x_691_);
v___x_693_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__1, &l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__1_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__1);
v___x_694_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__4));
lean_inc(v_currMacroScope_689_);
lean_inc(v_quotContext_688_);
v___x_695_ = l_Lean_addMacroScope(v_quotContext_688_, v___x_694_, v_currMacroScope_689_);
v___x_696_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__8));
v___x_697_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_697_, 0, v___x_692_);
lean_ctor_set(v___x_697_, 1, v___x_693_);
lean_ctor_set(v___x_697_, 2, v___x_695_);
lean_ctor_set(v___x_697_, 3, v___x_696_);
v___x_698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_698_, 0, v___x_697_);
lean_ctor_set(v___x_698_, 1, v_a_687_);
return v___x_698_;
}
case 1:
{
lean_object* v_quotContext_699_; lean_object* v_currMacroScope_700_; lean_object* v_ref_701_; uint8_t v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
v_quotContext_699_ = lean_ctor_get(v_a_686_, 1);
v_currMacroScope_700_ = lean_ctor_get(v_a_686_, 2);
v_ref_701_ = lean_ctor_get(v_a_686_, 5);
v___x_702_ = 0;
v___x_703_ = l_Lean_SourceInfo_fromRef(v_ref_701_, v___x_702_);
v___x_704_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__10, &l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__10_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__10);
v___x_705_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__12));
lean_inc(v_currMacroScope_700_);
lean_inc(v_quotContext_699_);
v___x_706_ = l_Lean_addMacroScope(v_quotContext_699_, v___x_705_, v_currMacroScope_700_);
v___x_707_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__16));
v___x_708_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_708_, 0, v___x_703_);
lean_ctor_set(v___x_708_, 1, v___x_704_);
lean_ctor_set(v___x_708_, 2, v___x_706_);
lean_ctor_set(v___x_708_, 3, v___x_707_);
v___x_709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_709_, 0, v___x_708_);
lean_ctor_set(v___x_709_, 1, v_a_687_);
return v___x_709_;
}
case 2:
{
lean_object* v_quotContext_710_; lean_object* v_currMacroScope_711_; lean_object* v_ref_712_; uint8_t v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
v_quotContext_710_ = lean_ctor_get(v_a_686_, 1);
v_currMacroScope_711_ = lean_ctor_get(v_a_686_, 2);
v_ref_712_ = lean_ctor_get(v_a_686_, 5);
v___x_713_ = 0;
v___x_714_ = l_Lean_SourceInfo_fromRef(v_ref_712_, v___x_713_);
v___x_715_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__18, &l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__18_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__18);
v___x_716_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__20));
lean_inc(v_currMacroScope_711_);
lean_inc(v_quotContext_710_);
v___x_717_ = l_Lean_addMacroScope(v_quotContext_710_, v___x_716_, v_currMacroScope_711_);
v___x_718_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__24));
v___x_719_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_719_, 0, v___x_714_);
lean_ctor_set(v___x_719_, 1, v___x_715_);
lean_ctor_set(v___x_719_, 2, v___x_717_);
lean_ctor_set(v___x_719_, 3, v___x_718_);
v___x_720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_720_, 0, v___x_719_);
lean_ctor_set(v___x_720_, 1, v_a_687_);
return v___x_720_;
}
case 3:
{
lean_object* v_quotContext_721_; lean_object* v_currMacroScope_722_; lean_object* v_ref_723_; uint8_t v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v_quotContext_721_ = lean_ctor_get(v_a_686_, 1);
v_currMacroScope_722_ = lean_ctor_get(v_a_686_, 2);
v_ref_723_ = lean_ctor_get(v_a_686_, 5);
v___x_724_ = 0;
v___x_725_ = l_Lean_SourceInfo_fromRef(v_ref_723_, v___x_724_);
v___x_726_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__26, &l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__26_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__26);
v___x_727_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__28));
lean_inc(v_currMacroScope_722_);
lean_inc(v_quotContext_721_);
v___x_728_ = l_Lean_addMacroScope(v_quotContext_721_, v___x_727_, v_currMacroScope_722_);
v___x_729_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__32));
v___x_730_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_730_, 0, v___x_725_);
lean_ctor_set(v___x_730_, 1, v___x_726_);
lean_ctor_set(v___x_730_, 2, v___x_728_);
lean_ctor_set(v___x_730_, 3, v___x_729_);
v___x_731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_731_, 0, v___x_730_);
lean_ctor_set(v___x_731_, 1, v_a_687_);
return v___x_731_;
}
default: 
{
lean_object* v_quotContext_732_; lean_object* v_currMacroScope_733_; lean_object* v_ref_734_; uint8_t v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; 
v_quotContext_732_ = lean_ctor_get(v_a_686_, 1);
v_currMacroScope_733_ = lean_ctor_get(v_a_686_, 2);
v_ref_734_ = lean_ctor_get(v_a_686_, 5);
v___x_735_ = 0;
v___x_736_ = l_Lean_SourceInfo_fromRef(v_ref_734_, v___x_735_);
v___x_737_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__34, &l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__34_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__34);
v___x_738_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__36));
lean_inc(v_currMacroScope_733_);
lean_inc(v_quotContext_732_);
v___x_739_ = l_Lean_addMacroScope(v_quotContext_732_, v___x_738_, v_currMacroScope_733_);
v___x_740_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__40));
v___x_741_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_741_, 0, v___x_736_);
lean_ctor_set(v___x_741_, 1, v___x_737_);
lean_ctor_set(v___x_741_, 2, v___x_739_);
lean_ctor_set(v___x_741_, 3, v___x_740_);
v___x_742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_742_, 0, v___x_741_);
lean_ctor_set(v___x_742_, 1, v_a_687_);
return v___x_742_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Time_Notation_0__Std_Time_convertOffsetX_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_685_ = stack[0].m_num;
lean_object* v_a_686_ = stack[1].m_obj;
lean_object* v_a_687_ = stack[2].m_obj;
lean_object* v_res_743_;
v_res_743_ = l___private_Std_Time_Notation_0__Std_Time_convertOffsetX(v_x_685_, v_a_686_, v_a_687_);
stack->m_obj
 = v_res_743_;
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___boxed(lean_object* v_x_744_, lean_object* v_a_745_, lean_object* v_a_746_){
_start:
{
uint8_t v_x_6614__boxed_747_; lean_object* v_res_748_; 
v_x_6614__boxed_747_ = lean_unbox(v_x_744_);
v_res_748_ = l___private_Std_Time_Notation_0__Std_Time_convertOffsetX(v_x_6614__boxed_747_, v_a_745_, v_a_746_);
lean_dec_ref(v_a_745_);
return v_res_748_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__1(void){
_start:
{
lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_750_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__0));
v___x_751_ = l_String_toRawSubstring_x27(v___x_750_);
return v___x_751_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__9(void){
_start:
{
lean_object* v___x_770_; lean_object* v___x_771_; 
v___x_770_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__8));
v___x_771_ = l_String_toRawSubstring_x27(v___x_770_);
return v___x_771_;
}
}
lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetO(uint8_t v_x_788_, lean_object* v_a_789_, lean_object* v_a_790_){
_start:
{
if (v_x_788_ == 0)
{
lean_object* v_quotContext_791_; lean_object* v_currMacroScope_792_; lean_object* v_ref_793_; uint8_t v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
v_quotContext_791_ = lean_ctor_get(v_a_789_, 1);
v_currMacroScope_792_ = lean_ctor_get(v_a_789_, 2);
v_ref_793_ = lean_ctor_get(v_a_789_, 5);
v___x_794_ = 0;
v___x_795_ = l_Lean_SourceInfo_fromRef(v_ref_793_, v___x_794_);
v___x_796_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__1, &l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__1_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__1);
v___x_797_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__3));
lean_inc(v_currMacroScope_792_);
lean_inc(v_quotContext_791_);
v___x_798_ = l_Lean_addMacroScope(v_quotContext_791_, v___x_797_, v_currMacroScope_792_);
v___x_799_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__7));
v___x_800_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_800_, 0, v___x_795_);
lean_ctor_set(v___x_800_, 1, v___x_796_);
lean_ctor_set(v___x_800_, 2, v___x_798_);
lean_ctor_set(v___x_800_, 3, v___x_799_);
v___x_801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_801_, 0, v___x_800_);
lean_ctor_set(v___x_801_, 1, v_a_790_);
return v___x_801_;
}
else
{
lean_object* v_quotContext_802_; lean_object* v_currMacroScope_803_; lean_object* v_ref_804_; uint8_t v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; 
v_quotContext_802_ = lean_ctor_get(v_a_789_, 1);
v_currMacroScope_803_ = lean_ctor_get(v_a_789_, 2);
v_ref_804_ = lean_ctor_get(v_a_789_, 5);
v___x_805_ = 0;
v___x_806_ = l_Lean_SourceInfo_fromRef(v_ref_804_, v___x_805_);
v___x_807_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__9, &l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__9_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__9);
v___x_808_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__10));
lean_inc(v_currMacroScope_803_);
lean_inc(v_quotContext_802_);
v___x_809_ = l_Lean_addMacroScope(v_quotContext_802_, v___x_808_, v_currMacroScope_803_);
v___x_810_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__14));
v___x_811_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_811_, 0, v___x_806_);
lean_ctor_set(v___x_811_, 1, v___x_807_);
lean_ctor_set(v___x_811_, 2, v___x_809_);
lean_ctor_set(v___x_811_, 3, v___x_810_);
v___x_812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_812_, 0, v___x_811_);
lean_ctor_set(v___x_812_, 1, v_a_790_);
return v___x_812_;
}
}
}
LEAN_EXPORT void l___private_Std_Time_Notation_0__Std_Time_convertOffsetO_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_788_ = stack[0].m_num;
lean_object* v_a_789_ = stack[1].m_obj;
lean_object* v_a_790_ = stack[2].m_obj;
lean_object* v_res_813_;
v_res_813_ = l___private_Std_Time_Notation_0__Std_Time_convertOffsetO(v_x_788_, v_a_789_, v_a_790_);
stack->m_obj
 = v_res_813_;
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___boxed(lean_object* v_x_814_, lean_object* v_a_815_, lean_object* v_a_816_){
_start:
{
uint8_t v_x_2649__boxed_817_; lean_object* v_res_818_; 
v_x_2649__boxed_817_ = lean_unbox(v_x_814_);
v_res_818_ = l___private_Std_Time_Notation_0__Std_Time_convertOffsetO(v_x_2649__boxed_817_, v_a_815_, v_a_816_);
lean_dec_ref(v_a_815_);
return v_res_818_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__1(void){
_start:
{
lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_820_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__0));
v___x_821_ = l_String_toRawSubstring_x27(v___x_820_);
return v___x_821_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__9(void){
_start:
{
lean_object* v___x_840_; lean_object* v___x_841_; 
v___x_840_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__8));
v___x_841_ = l_String_toRawSubstring_x27(v___x_840_);
return v___x_841_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__16(void){
_start:
{
lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_859_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__15));
v___x_860_ = l_String_toRawSubstring_x27(v___x_859_);
return v___x_860_;
}
}
lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ(uint8_t v_x_877_, lean_object* v_a_878_, lean_object* v_a_879_){
_start:
{
switch(v_x_877_)
{
case 0:
{
lean_object* v_quotContext_880_; lean_object* v_currMacroScope_881_; lean_object* v_ref_882_; uint8_t v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
v_quotContext_880_ = lean_ctor_get(v_a_878_, 1);
v_currMacroScope_881_ = lean_ctor_get(v_a_878_, 2);
v_ref_882_ = lean_ctor_get(v_a_878_, 5);
v___x_883_ = 0;
v___x_884_ = l_Lean_SourceInfo_fromRef(v_ref_882_, v___x_883_);
v___x_885_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__1, &l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__1_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__1);
v___x_886_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__3));
lean_inc(v_currMacroScope_881_);
lean_inc(v_quotContext_880_);
v___x_887_ = l_Lean_addMacroScope(v_quotContext_880_, v___x_886_, v_currMacroScope_881_);
v___x_888_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__7));
v___x_889_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_889_, 0, v___x_884_);
lean_ctor_set(v___x_889_, 1, v___x_885_);
lean_ctor_set(v___x_889_, 2, v___x_887_);
lean_ctor_set(v___x_889_, 3, v___x_888_);
v___x_890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_890_, 0, v___x_889_);
lean_ctor_set(v___x_890_, 1, v_a_879_);
return v___x_890_;
}
case 1:
{
lean_object* v_quotContext_891_; lean_object* v_currMacroScope_892_; lean_object* v_ref_893_; uint8_t v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
v_quotContext_891_ = lean_ctor_get(v_a_878_, 1);
v_currMacroScope_892_ = lean_ctor_get(v_a_878_, 2);
v_ref_893_ = lean_ctor_get(v_a_878_, 5);
v___x_894_ = 0;
v___x_895_ = l_Lean_SourceInfo_fromRef(v_ref_893_, v___x_894_);
v___x_896_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__9, &l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__9_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__9);
v___x_897_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__10));
lean_inc(v_currMacroScope_892_);
lean_inc(v_quotContext_891_);
v___x_898_ = l_Lean_addMacroScope(v_quotContext_891_, v___x_897_, v_currMacroScope_892_);
v___x_899_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__14));
v___x_900_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_900_, 0, v___x_895_);
lean_ctor_set(v___x_900_, 1, v___x_896_);
lean_ctor_set(v___x_900_, 2, v___x_898_);
lean_ctor_set(v___x_900_, 3, v___x_899_);
v___x_901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_901_, 0, v___x_900_);
lean_ctor_set(v___x_901_, 1, v_a_879_);
return v___x_901_;
}
default: 
{
lean_object* v_quotContext_902_; lean_object* v_currMacroScope_903_; lean_object* v_ref_904_; uint8_t v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
v_quotContext_902_ = lean_ctor_get(v_a_878_, 1);
v_currMacroScope_903_ = lean_ctor_get(v_a_878_, 2);
v_ref_904_ = lean_ctor_get(v_a_878_, 5);
v___x_905_ = 0;
v___x_906_ = l_Lean_SourceInfo_fromRef(v_ref_904_, v___x_905_);
v___x_907_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__16, &l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__16_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__16);
v___x_908_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__17));
lean_inc(v_currMacroScope_903_);
lean_inc(v_quotContext_902_);
v___x_909_ = l_Lean_addMacroScope(v_quotContext_902_, v___x_908_, v_currMacroScope_903_);
v___x_910_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__21));
v___x_911_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_911_, 0, v___x_906_);
lean_ctor_set(v___x_911_, 1, v___x_907_);
lean_ctor_set(v___x_911_, 2, v___x_909_);
lean_ctor_set(v___x_911_, 3, v___x_910_);
v___x_912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_912_, 0, v___x_911_);
lean_ctor_set(v___x_912_, 1, v_a_879_);
return v___x_912_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_877_ = stack[0].m_num;
lean_object* v_a_878_ = stack[1].m_obj;
lean_object* v_a_879_ = stack[2].m_obj;
lean_object* v_res_913_;
v_res_913_ = l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ(v_x_877_, v_a_878_, v_a_879_);
stack->m_obj
 = v_res_913_;
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___boxed(lean_object* v_x_914_, lean_object* v_a_915_, lean_object* v_a_916_){
_start:
{
uint8_t v_x_3969__boxed_917_; lean_object* v_res_918_; 
v_x_3969__boxed_917_ = lean_unbox(v_x_914_);
v_res_918_ = l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ(v_x_3969__boxed_917_, v_a_915_, v_a_916_);
lean_dec_ref(v_a_915_);
return v_res_918_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__1(void){
_start:
{
lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_920_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__0));
v___x_921_ = l_String_toRawSubstring_x27(v___x_920_);
return v___x_921_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__10(void){
_start:
{
lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_941_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__9));
v___x_942_ = l_String_toRawSubstring_x27(v___x_941_);
return v___x_942_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__18(void){
_start:
{
lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_961_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__17));
v___x_962_ = l_String_toRawSubstring_x27(v___x_961_);
return v___x_962_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__26(void){
_start:
{
lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_981_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__25));
v___x_982_ = l_String_toRawSubstring_x27(v___x_981_);
return v___x_982_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__34(void){
_start:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_1001_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__33));
v___x_1002_ = l_String_toRawSubstring_x27(v___x_1001_);
return v___x_1002_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49(void){
_start:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1037_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__48));
v___x_1038_ = l_String_toRawSubstring_x27(v___x_1037_);
return v___x_1038_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__70(void){
_start:
{
lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___x_1087_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__69));
v___x_1088_ = l_String_toRawSubstring_x27(v___x_1087_);
return v___x_1088_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__74(void){
_start:
{
lean_object* v___x_1093_; lean_object* v___x_1094_; 
v___x_1093_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__73));
v___x_1094_ = l_String_toRawSubstring_x27(v___x_1093_);
return v___x_1094_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__77(void){
_start:
{
lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1098_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__76));
v___x_1099_ = l_String_toRawSubstring_x27(v___x_1098_);
return v___x_1099_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__85(void){
_start:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1118_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__84));
v___x_1119_ = l_String_toRawSubstring_x27(v___x_1118_);
return v___x_1119_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__93(void){
_start:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1138_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__92));
v___x_1139_ = l_String_toRawSubstring_x27(v___x_1138_);
return v___x_1139_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__101(void){
_start:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1158_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__100));
v___x_1159_ = l_String_toRawSubstring_x27(v___x_1158_);
return v___x_1159_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__109(void){
_start:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; 
v___x_1178_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__108));
v___x_1179_ = l_String_toRawSubstring_x27(v___x_1178_);
return v___x_1179_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__117(void){
_start:
{
lean_object* v___x_1198_; lean_object* v___x_1199_; 
v___x_1198_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__116));
v___x_1199_ = l_String_toRawSubstring_x27(v___x_1198_);
return v___x_1199_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__125(void){
_start:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; 
v___x_1218_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__124));
v___x_1219_ = l_String_toRawSubstring_x27(v___x_1218_);
return v___x_1219_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__133(void){
_start:
{
lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___x_1238_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__132));
v___x_1239_ = l_String_toRawSubstring_x27(v___x_1238_);
return v___x_1239_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__141(void){
_start:
{
lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1258_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__140));
v___x_1259_ = l_String_toRawSubstring_x27(v___x_1258_);
return v___x_1259_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__149(void){
_start:
{
lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1278_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__148));
v___x_1279_ = l_String_toRawSubstring_x27(v___x_1278_);
return v___x_1279_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__157(void){
_start:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; 
v___x_1298_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__156));
v___x_1299_ = l_String_toRawSubstring_x27(v___x_1298_);
return v___x_1299_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__165(void){
_start:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1318_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__164));
v___x_1319_ = l_String_toRawSubstring_x27(v___x_1318_);
return v___x_1319_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__173(void){
_start:
{
lean_object* v___x_1338_; lean_object* v___x_1339_; 
v___x_1338_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__172));
v___x_1339_ = l_String_toRawSubstring_x27(v___x_1338_);
return v___x_1339_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__181(void){
_start:
{
lean_object* v___x_1358_; lean_object* v___x_1359_; 
v___x_1358_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__180));
v___x_1359_ = l_String_toRawSubstring_x27(v___x_1358_);
return v___x_1359_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__189(void){
_start:
{
lean_object* v___x_1378_; lean_object* v___x_1379_; 
v___x_1378_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__188));
v___x_1379_ = l_String_toRawSubstring_x27(v___x_1378_);
return v___x_1379_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__197(void){
_start:
{
lean_object* v___x_1398_; lean_object* v___x_1399_; 
v___x_1398_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__196));
v___x_1399_ = l_String_toRawSubstring_x27(v___x_1398_);
return v___x_1399_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__205(void){
_start:
{
lean_object* v___x_1418_; lean_object* v___x_1419_; 
v___x_1418_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__204));
v___x_1419_ = l_String_toRawSubstring_x27(v___x_1418_);
return v___x_1419_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__213(void){
_start:
{
lean_object* v___x_1438_; lean_object* v___x_1439_; 
v___x_1438_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__212));
v___x_1439_ = l_String_toRawSubstring_x27(v___x_1438_);
return v___x_1439_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__221(void){
_start:
{
lean_object* v___x_1458_; lean_object* v___x_1459_; 
v___x_1458_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__220));
v___x_1459_ = l_String_toRawSubstring_x27(v___x_1458_);
return v___x_1459_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__229(void){
_start:
{
lean_object* v___x_1478_; lean_object* v___x_1479_; 
v___x_1478_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__228));
v___x_1479_ = l_String_toRawSubstring_x27(v___x_1478_);
return v___x_1479_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__237(void){
_start:
{
lean_object* v___x_1498_; lean_object* v___x_1499_; 
v___x_1498_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__236));
v___x_1499_ = l_String_toRawSubstring_x27(v___x_1498_);
return v___x_1499_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__245(void){
_start:
{
lean_object* v___x_1518_; lean_object* v___x_1519_; 
v___x_1518_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__244));
v___x_1519_ = l_String_toRawSubstring_x27(v___x_1518_);
return v___x_1519_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__253(void){
_start:
{
lean_object* v___x_1538_; lean_object* v___x_1539_; 
v___x_1538_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__252));
v___x_1539_ = l_String_toRawSubstring_x27(v___x_1538_);
return v___x_1539_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__261(void){
_start:
{
lean_object* v___x_1558_; lean_object* v___x_1559_; 
v___x_1558_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__260));
v___x_1559_ = l_String_toRawSubstring_x27(v___x_1558_);
return v___x_1559_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__269(void){
_start:
{
lean_object* v___x_1578_; lean_object* v___x_1579_; 
v___x_1578_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__268));
v___x_1579_ = l_String_toRawSubstring_x27(v___x_1578_);
return v___x_1579_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__277(void){
_start:
{
lean_object* v___x_1598_; lean_object* v___x_1599_; 
v___x_1598_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__276));
v___x_1599_ = l_String_toRawSubstring_x27(v___x_1598_);
return v___x_1599_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__285(void){
_start:
{
lean_object* v___x_1618_; lean_object* v___x_1619_; 
v___x_1618_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__284));
v___x_1619_ = l_String_toRawSubstring_x27(v___x_1618_);
return v___x_1619_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__293(void){
_start:
{
lean_object* v___x_1638_; lean_object* v___x_1639_; 
v___x_1638_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__292));
v___x_1639_ = l_String_toRawSubstring_x27(v___x_1638_);
return v___x_1639_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__301(void){
_start:
{
lean_object* v___x_1658_; lean_object* v___x_1659_; 
v___x_1658_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__300));
v___x_1659_ = l_String_toRawSubstring_x27(v___x_1658_);
return v___x_1659_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__309(void){
_start:
{
lean_object* v___x_1678_; lean_object* v___x_1679_; 
v___x_1678_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__308));
v___x_1679_ = l_String_toRawSubstring_x27(v___x_1678_);
return v___x_1679_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__317(void){
_start:
{
lean_object* v___x_1698_; lean_object* v___x_1699_; 
v___x_1698_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__316));
v___x_1699_ = l_String_toRawSubstring_x27(v___x_1698_);
return v___x_1699_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier(lean_object* v_x_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_){
_start:
{
switch(lean_obj_tag(v_x_1717_))
{
case 0:
{
uint8_t v_presentation_1720_; lean_object* v___x_1721_; lean_object* v_a_1722_; lean_object* v_a_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1744_; 
v_presentation_1720_ = lean_ctor_get_uint8(v_x_1717_, 0);
lean_dec_ref_known(v_x_1717_, 0);
v___x_1721_ = l___private_Std_Time_Notation_0__Std_Time_convertText(v_presentation_1720_, v_a_1718_, v_a_1719_);
v_a_1722_ = lean_ctor_get(v___x_1721_, 0);
v_a_1723_ = lean_ctor_get(v___x_1721_, 1);
v_isSharedCheck_1744_ = !lean_is_exclusive(v___x_1721_);
if (v_isSharedCheck_1744_ == 0)
{
v___x_1725_ = v___x_1721_;
v_isShared_1726_ = v_isSharedCheck_1744_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_a_1723_);
lean_inc(v_a_1722_);
lean_dec(v___x_1721_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1744_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
lean_object* v_quotContext_1727_; lean_object* v_currMacroScope_1728_; lean_object* v_ref_1729_; uint8_t v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1742_; 
v_quotContext_1727_ = lean_ctor_get(v_a_1718_, 1);
v_currMacroScope_1728_ = lean_ctor_get(v_a_1718_, 2);
v_ref_1729_ = lean_ctor_get(v_a_1718_, 5);
v___x_1730_ = 0;
v___x_1731_ = l_Lean_SourceInfo_fromRef(v_ref_1729_, v___x_1730_);
v___x_1732_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_1733_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__1, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__1_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__1);
v___x_1734_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__4));
lean_inc(v_currMacroScope_1728_);
lean_inc(v_quotContext_1727_);
v___x_1735_ = l_Lean_addMacroScope(v_quotContext_1727_, v___x_1734_, v_currMacroScope_1728_);
v___x_1736_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__8));
lean_inc_n(v___x_1731_, 2);
v___x_1737_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1737_, 0, v___x_1731_);
lean_ctor_set(v___x_1737_, 1, v___x_1733_);
lean_ctor_set(v___x_1737_, 2, v___x_1735_);
lean_ctor_set(v___x_1737_, 3, v___x_1736_);
v___x_1738_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_1739_ = l_Lean_Syntax_node1(v___x_1731_, v___x_1738_, v_a_1722_);
v___x_1740_ = l_Lean_Syntax_node2(v___x_1731_, v___x_1732_, v___x_1737_, v___x_1739_);
if (v_isShared_1726_ == 0)
{
lean_ctor_set(v___x_1725_, 0, v___x_1740_);
v___x_1742_ = v___x_1725_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v___x_1740_);
lean_ctor_set(v_reuseFailAlloc_1743_, 1, v_a_1723_);
v___x_1742_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1741_;
}
v_reusejp_1741_:
{
return v___x_1742_;
}
}
}
case 1:
{
lean_object* v_presentation_1745_; lean_object* v___x_1746_; lean_object* v_a_1747_; lean_object* v_a_1748_; lean_object* v___x_1750_; uint8_t v_isShared_1751_; uint8_t v_isSharedCheck_1769_; 
v_presentation_1745_ = lean_ctor_get(v_x_1717_, 0);
lean_inc(v_presentation_1745_);
lean_dec_ref_known(v_x_1717_, 1);
v___x_1746_ = l___private_Std_Time_Notation_0__Std_Time_convertYear(v_presentation_1745_, v_a_1718_, v_a_1719_);
v_a_1747_ = lean_ctor_get(v___x_1746_, 0);
v_a_1748_ = lean_ctor_get(v___x_1746_, 1);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1746_);
if (v_isSharedCheck_1769_ == 0)
{
v___x_1750_ = v___x_1746_;
v_isShared_1751_ = v_isSharedCheck_1769_;
goto v_resetjp_1749_;
}
else
{
lean_inc(v_a_1748_);
lean_inc(v_a_1747_);
lean_dec(v___x_1746_);
v___x_1750_ = lean_box(0);
v_isShared_1751_ = v_isSharedCheck_1769_;
goto v_resetjp_1749_;
}
v_resetjp_1749_:
{
lean_object* v_quotContext_1752_; lean_object* v_currMacroScope_1753_; lean_object* v_ref_1754_; uint8_t v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1767_; 
v_quotContext_1752_ = lean_ctor_get(v_a_1718_, 1);
v_currMacroScope_1753_ = lean_ctor_get(v_a_1718_, 2);
v_ref_1754_ = lean_ctor_get(v_a_1718_, 5);
v___x_1755_ = 0;
v___x_1756_ = l_Lean_SourceInfo_fromRef(v_ref_1754_, v___x_1755_);
v___x_1757_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_1758_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__10, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__10_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__10);
v___x_1759_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__12));
lean_inc(v_currMacroScope_1753_);
lean_inc(v_quotContext_1752_);
v___x_1760_ = l_Lean_addMacroScope(v_quotContext_1752_, v___x_1759_, v_currMacroScope_1753_);
v___x_1761_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__16));
lean_inc_n(v___x_1756_, 2);
v___x_1762_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1762_, 0, v___x_1756_);
lean_ctor_set(v___x_1762_, 1, v___x_1758_);
lean_ctor_set(v___x_1762_, 2, v___x_1760_);
lean_ctor_set(v___x_1762_, 3, v___x_1761_);
v___x_1763_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_1764_ = l_Lean_Syntax_node1(v___x_1756_, v___x_1763_, v_a_1747_);
v___x_1765_ = l_Lean_Syntax_node2(v___x_1756_, v___x_1757_, v___x_1762_, v___x_1764_);
if (v_isShared_1751_ == 0)
{
lean_ctor_set(v___x_1750_, 0, v___x_1765_);
v___x_1767_ = v___x_1750_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v___x_1765_);
lean_ctor_set(v_reuseFailAlloc_1768_, 1, v_a_1748_);
v___x_1767_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
return v___x_1767_;
}
}
}
case 2:
{
lean_object* v_presentation_1770_; lean_object* v___x_1771_; lean_object* v_a_1772_; lean_object* v_a_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1794_; 
v_presentation_1770_ = lean_ctor_get(v_x_1717_, 0);
lean_inc(v_presentation_1770_);
lean_dec_ref_known(v_x_1717_, 1);
v___x_1771_ = l___private_Std_Time_Notation_0__Std_Time_convertYear(v_presentation_1770_, v_a_1718_, v_a_1719_);
v_a_1772_ = lean_ctor_get(v___x_1771_, 0);
v_a_1773_ = lean_ctor_get(v___x_1771_, 1);
v_isSharedCheck_1794_ = !lean_is_exclusive(v___x_1771_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1775_ = v___x_1771_;
v_isShared_1776_ = v_isSharedCheck_1794_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_a_1773_);
lean_inc(v_a_1772_);
lean_dec(v___x_1771_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1794_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v_quotContext_1777_; lean_object* v_currMacroScope_1778_; lean_object* v_ref_1779_; uint8_t v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1792_; 
v_quotContext_1777_ = lean_ctor_get(v_a_1718_, 1);
v_currMacroScope_1778_ = lean_ctor_get(v_a_1718_, 2);
v_ref_1779_ = lean_ctor_get(v_a_1718_, 5);
v___x_1780_ = 0;
v___x_1781_ = l_Lean_SourceInfo_fromRef(v_ref_1779_, v___x_1780_);
v___x_1782_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_1783_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__18, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__18_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__18);
v___x_1784_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__20));
lean_inc(v_currMacroScope_1778_);
lean_inc(v_quotContext_1777_);
v___x_1785_ = l_Lean_addMacroScope(v_quotContext_1777_, v___x_1784_, v_currMacroScope_1778_);
v___x_1786_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__24));
lean_inc_n(v___x_1781_, 2);
v___x_1787_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1787_, 0, v___x_1781_);
lean_ctor_set(v___x_1787_, 1, v___x_1783_);
lean_ctor_set(v___x_1787_, 2, v___x_1785_);
lean_ctor_set(v___x_1787_, 3, v___x_1786_);
v___x_1788_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_1789_ = l_Lean_Syntax_node1(v___x_1781_, v___x_1788_, v_a_1772_);
v___x_1790_ = l_Lean_Syntax_node2(v___x_1781_, v___x_1782_, v___x_1787_, v___x_1789_);
if (v_isShared_1776_ == 0)
{
lean_ctor_set(v___x_1775_, 0, v___x_1790_);
v___x_1792_ = v___x_1775_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v___x_1790_);
lean_ctor_set(v_reuseFailAlloc_1793_, 1, v_a_1773_);
v___x_1792_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
return v___x_1792_;
}
}
}
case 3:
{
lean_object* v_presentation_1795_; lean_object* v___x_1796_; lean_object* v_a_1797_; lean_object* v_a_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1819_; 
v_presentation_1795_ = lean_ctor_get(v_x_1717_, 0);
lean_inc(v_presentation_1795_);
lean_dec_ref_known(v_x_1717_, 1);
v___x_1796_ = l___private_Std_Time_Notation_0__Std_Time_convertNumber(v_presentation_1795_, v_a_1718_, v_a_1719_);
v_a_1797_ = lean_ctor_get(v___x_1796_, 0);
v_a_1798_ = lean_ctor_get(v___x_1796_, 1);
v_isSharedCheck_1819_ = !lean_is_exclusive(v___x_1796_);
if (v_isSharedCheck_1819_ == 0)
{
v___x_1800_ = v___x_1796_;
v_isShared_1801_ = v_isSharedCheck_1819_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_a_1798_);
lean_inc(v_a_1797_);
lean_dec(v___x_1796_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1819_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
lean_object* v_quotContext_1802_; lean_object* v_currMacroScope_1803_; lean_object* v_ref_1804_; uint8_t v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1817_; 
v_quotContext_1802_ = lean_ctor_get(v_a_1718_, 1);
v_currMacroScope_1803_ = lean_ctor_get(v_a_1718_, 2);
v_ref_1804_ = lean_ctor_get(v_a_1718_, 5);
v___x_1805_ = 0;
v___x_1806_ = l_Lean_SourceInfo_fromRef(v_ref_1804_, v___x_1805_);
v___x_1807_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_1808_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__26, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__26_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__26);
v___x_1809_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__28));
lean_inc(v_currMacroScope_1803_);
lean_inc(v_quotContext_1802_);
v___x_1810_ = l_Lean_addMacroScope(v_quotContext_1802_, v___x_1809_, v_currMacroScope_1803_);
v___x_1811_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__32));
lean_inc_n(v___x_1806_, 2);
v___x_1812_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1812_, 0, v___x_1806_);
lean_ctor_set(v___x_1812_, 1, v___x_1808_);
lean_ctor_set(v___x_1812_, 2, v___x_1810_);
lean_ctor_set(v___x_1812_, 3, v___x_1811_);
v___x_1813_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_1814_ = l_Lean_Syntax_node1(v___x_1806_, v___x_1813_, v_a_1797_);
v___x_1815_ = l_Lean_Syntax_node2(v___x_1806_, v___x_1807_, v___x_1812_, v___x_1814_);
if (v_isShared_1801_ == 0)
{
lean_ctor_set(v___x_1800_, 0, v___x_1815_);
v___x_1817_ = v___x_1800_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v___x_1815_);
lean_ctor_set(v_reuseFailAlloc_1818_, 1, v_a_1798_);
v___x_1817_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
return v___x_1817_;
}
}
}
case 4:
{
lean_object* v_presentation_1820_; 
v_presentation_1820_ = lean_ctor_get(v_x_1717_, 0);
lean_inc_ref(v_presentation_1820_);
lean_dec_ref_known(v_x_1717_, 1);
if (lean_obj_tag(v_presentation_1820_) == 0)
{
lean_object* v_val_1821_; lean_object* v___x_1822_; lean_object* v_a_1823_; lean_object* v_a_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1871_; 
v_val_1821_ = lean_ctor_get(v_presentation_1820_, 0);
lean_inc(v_val_1821_);
lean_dec_ref_known(v_presentation_1820_, 1);
v___x_1822_ = l___private_Std_Time_Notation_0__Std_Time_convertNumber(v_val_1821_, v_a_1718_, v_a_1719_);
v_a_1823_ = lean_ctor_get(v___x_1822_, 0);
v_a_1824_ = lean_ctor_get(v___x_1822_, 1);
v_isSharedCheck_1871_ = !lean_is_exclusive(v___x_1822_);
if (v_isSharedCheck_1871_ == 0)
{
v___x_1826_ = v___x_1822_;
v_isShared_1827_ = v_isSharedCheck_1871_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_a_1824_);
lean_inc(v_a_1823_);
lean_dec(v___x_1822_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1871_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v_quotContext_1828_; lean_object* v_currMacroScope_1829_; lean_object* v_ref_1830_; uint8_t v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1869_; 
v_quotContext_1828_ = lean_ctor_get(v_a_1718_, 1);
v_currMacroScope_1829_ = lean_ctor_get(v_a_1718_, 2);
v_ref_1830_ = lean_ctor_get(v_a_1718_, 5);
v___x_1831_ = 0;
v___x_1832_ = l_Lean_SourceInfo_fromRef(v_ref_1830_, v___x_1831_);
v___x_1833_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_1834_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__34, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__34_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__34);
v___x_1835_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__36));
lean_inc_n(v_currMacroScope_1829_, 3);
lean_inc_n(v_quotContext_1828_, 3);
v___x_1836_ = l_Lean_addMacroScope(v_quotContext_1828_, v___x_1835_, v_currMacroScope_1829_);
v___x_1837_ = lean_box(0);
v___x_1838_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__40));
lean_inc_n(v___x_1832_, 13);
v___x_1839_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1839_, 0, v___x_1832_);
lean_ctor_set(v___x_1839_, 1, v___x_1834_);
lean_ctor_set(v___x_1839_, 2, v___x_1836_);
lean_ctor_set(v___x_1839_, 3, v___x_1838_);
v___x_1840_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_1841_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__42));
v___x_1842_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__44));
v___x_1843_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__45));
v___x_1844_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1832_);
lean_ctor_set(v___x_1844_, 1, v___x_1843_);
v___x_1845_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__47));
v___x_1846_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49);
v___x_1847_ = lean_box(0);
v___x_1848_ = l_Lean_addMacroScope(v_quotContext_1828_, v___x_1847_, v_currMacroScope_1829_);
v___x_1849_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__65));
v___x_1850_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1850_, 0, v___x_1832_);
lean_ctor_set(v___x_1850_, 1, v___x_1846_);
lean_ctor_set(v___x_1850_, 2, v___x_1848_);
lean_ctor_set(v___x_1850_, 3, v___x_1849_);
v___x_1851_ = l_Lean_Syntax_node1(v___x_1832_, v___x_1845_, v___x_1850_);
v___x_1852_ = l_Lean_Syntax_node2(v___x_1832_, v___x_1842_, v___x_1844_, v___x_1851_);
v___x_1853_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__67));
v___x_1854_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__68));
v___x_1855_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1855_, 0, v___x_1832_);
lean_ctor_set(v___x_1855_, 1, v___x_1854_);
v___x_1856_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__70, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__70_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__70);
v___x_1857_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__71));
v___x_1858_ = l_Lean_addMacroScope(v_quotContext_1828_, v___x_1857_, v_currMacroScope_1829_);
v___x_1859_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1859_, 0, v___x_1832_);
lean_ctor_set(v___x_1859_, 1, v___x_1856_);
lean_ctor_set(v___x_1859_, 2, v___x_1858_);
lean_ctor_set(v___x_1859_, 3, v___x_1837_);
v___x_1860_ = l_Lean_Syntax_node2(v___x_1832_, v___x_1853_, v___x_1855_, v___x_1859_);
v___x_1861_ = l_Lean_Syntax_node1(v___x_1832_, v___x_1840_, v_a_1823_);
v___x_1862_ = l_Lean_Syntax_node2(v___x_1832_, v___x_1833_, v___x_1860_, v___x_1861_);
v___x_1863_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__72));
v___x_1864_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1864_, 0, v___x_1832_);
lean_ctor_set(v___x_1864_, 1, v___x_1863_);
v___x_1865_ = l_Lean_Syntax_node3(v___x_1832_, v___x_1841_, v___x_1852_, v___x_1862_, v___x_1864_);
v___x_1866_ = l_Lean_Syntax_node1(v___x_1832_, v___x_1840_, v___x_1865_);
v___x_1867_ = l_Lean_Syntax_node2(v___x_1832_, v___x_1833_, v___x_1839_, v___x_1866_);
if (v_isShared_1827_ == 0)
{
lean_ctor_set(v___x_1826_, 0, v___x_1867_);
v___x_1869_ = v___x_1826_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v___x_1867_);
lean_ctor_set(v_reuseFailAlloc_1870_, 1, v_a_1824_);
v___x_1869_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
return v___x_1869_;
}
}
}
else
{
lean_object* v_val_1872_; uint8_t v___x_1873_; lean_object* v___x_1874_; lean_object* v_a_1875_; lean_object* v_a_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1923_; 
v_val_1872_ = lean_ctor_get(v_presentation_1820_, 0);
lean_inc(v_val_1872_);
lean_dec_ref_known(v_presentation_1820_, 1);
v___x_1873_ = lean_unbox(v_val_1872_);
lean_dec(v_val_1872_);
v___x_1874_ = l___private_Std_Time_Notation_0__Std_Time_convertText(v___x_1873_, v_a_1718_, v_a_1719_);
v_a_1875_ = lean_ctor_get(v___x_1874_, 0);
v_a_1876_ = lean_ctor_get(v___x_1874_, 1);
v_isSharedCheck_1923_ = !lean_is_exclusive(v___x_1874_);
if (v_isSharedCheck_1923_ == 0)
{
v___x_1878_ = v___x_1874_;
v_isShared_1879_ = v_isSharedCheck_1923_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_a_1876_);
lean_inc(v_a_1875_);
lean_dec(v___x_1874_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1923_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v_quotContext_1880_; lean_object* v_currMacroScope_1881_; lean_object* v_ref_1882_; uint8_t v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1921_; 
v_quotContext_1880_ = lean_ctor_get(v_a_1718_, 1);
v_currMacroScope_1881_ = lean_ctor_get(v_a_1718_, 2);
v_ref_1882_ = lean_ctor_get(v_a_1718_, 5);
v___x_1883_ = 0;
v___x_1884_ = l_Lean_SourceInfo_fromRef(v_ref_1882_, v___x_1883_);
v___x_1885_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_1886_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__34, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__34_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__34);
v___x_1887_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__36));
lean_inc_n(v_currMacroScope_1881_, 3);
lean_inc_n(v_quotContext_1880_, 3);
v___x_1888_ = l_Lean_addMacroScope(v_quotContext_1880_, v___x_1887_, v_currMacroScope_1881_);
v___x_1889_ = lean_box(0);
v___x_1890_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__40));
lean_inc_n(v___x_1884_, 13);
v___x_1891_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1891_, 0, v___x_1884_);
lean_ctor_set(v___x_1891_, 1, v___x_1886_);
lean_ctor_set(v___x_1891_, 2, v___x_1888_);
lean_ctor_set(v___x_1891_, 3, v___x_1890_);
v___x_1892_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_1893_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__42));
v___x_1894_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__44));
v___x_1895_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__45));
v___x_1896_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1896_, 0, v___x_1884_);
lean_ctor_set(v___x_1896_, 1, v___x_1895_);
v___x_1897_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__47));
v___x_1898_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49);
v___x_1899_ = lean_box(0);
v___x_1900_ = l_Lean_addMacroScope(v_quotContext_1880_, v___x_1899_, v_currMacroScope_1881_);
v___x_1901_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__65));
v___x_1902_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1902_, 0, v___x_1884_);
lean_ctor_set(v___x_1902_, 1, v___x_1898_);
lean_ctor_set(v___x_1902_, 2, v___x_1900_);
lean_ctor_set(v___x_1902_, 3, v___x_1901_);
v___x_1903_ = l_Lean_Syntax_node1(v___x_1884_, v___x_1897_, v___x_1902_);
v___x_1904_ = l_Lean_Syntax_node2(v___x_1884_, v___x_1894_, v___x_1896_, v___x_1903_);
v___x_1905_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__67));
v___x_1906_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__68));
v___x_1907_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1907_, 0, v___x_1884_);
lean_ctor_set(v___x_1907_, 1, v___x_1906_);
v___x_1908_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__74, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__74_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__74);
v___x_1909_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__75));
v___x_1910_ = l_Lean_addMacroScope(v_quotContext_1880_, v___x_1909_, v_currMacroScope_1881_);
v___x_1911_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1911_, 0, v___x_1884_);
lean_ctor_set(v___x_1911_, 1, v___x_1908_);
lean_ctor_set(v___x_1911_, 2, v___x_1910_);
lean_ctor_set(v___x_1911_, 3, v___x_1889_);
v___x_1912_ = l_Lean_Syntax_node2(v___x_1884_, v___x_1905_, v___x_1907_, v___x_1911_);
v___x_1913_ = l_Lean_Syntax_node1(v___x_1884_, v___x_1892_, v_a_1875_);
v___x_1914_ = l_Lean_Syntax_node2(v___x_1884_, v___x_1885_, v___x_1912_, v___x_1913_);
v___x_1915_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__72));
v___x_1916_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1916_, 0, v___x_1884_);
lean_ctor_set(v___x_1916_, 1, v___x_1915_);
v___x_1917_ = l_Lean_Syntax_node3(v___x_1884_, v___x_1893_, v___x_1904_, v___x_1914_, v___x_1916_);
v___x_1918_ = l_Lean_Syntax_node1(v___x_1884_, v___x_1892_, v___x_1917_);
v___x_1919_ = l_Lean_Syntax_node2(v___x_1884_, v___x_1885_, v___x_1891_, v___x_1918_);
if (v_isShared_1879_ == 0)
{
lean_ctor_set(v___x_1878_, 0, v___x_1919_);
v___x_1921_ = v___x_1878_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v___x_1919_);
lean_ctor_set(v_reuseFailAlloc_1922_, 1, v_a_1876_);
v___x_1921_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
return v___x_1921_;
}
}
}
}
case 5:
{
lean_object* v_presentation_1924_; 
v_presentation_1924_ = lean_ctor_get(v_x_1717_, 0);
lean_inc_ref(v_presentation_1924_);
lean_dec_ref_known(v_x_1717_, 1);
if (lean_obj_tag(v_presentation_1924_) == 0)
{
lean_object* v_val_1925_; lean_object* v___x_1926_; lean_object* v_a_1927_; lean_object* v_a_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1975_; 
v_val_1925_ = lean_ctor_get(v_presentation_1924_, 0);
lean_inc(v_val_1925_);
lean_dec_ref_known(v_presentation_1924_, 1);
v___x_1926_ = l___private_Std_Time_Notation_0__Std_Time_convertNumber(v_val_1925_, v_a_1718_, v_a_1719_);
v_a_1927_ = lean_ctor_get(v___x_1926_, 0);
v_a_1928_ = lean_ctor_get(v___x_1926_, 1);
v_isSharedCheck_1975_ = !lean_is_exclusive(v___x_1926_);
if (v_isSharedCheck_1975_ == 0)
{
v___x_1930_ = v___x_1926_;
v_isShared_1931_ = v_isSharedCheck_1975_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_a_1928_);
lean_inc(v_a_1927_);
lean_dec(v___x_1926_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1975_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v_quotContext_1932_; lean_object* v_currMacroScope_1933_; lean_object* v_ref_1934_; uint8_t v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1973_; 
v_quotContext_1932_ = lean_ctor_get(v_a_1718_, 1);
v_currMacroScope_1933_ = lean_ctor_get(v_a_1718_, 2);
v_ref_1934_ = lean_ctor_get(v_a_1718_, 5);
v___x_1935_ = 0;
v___x_1936_ = l_Lean_SourceInfo_fromRef(v_ref_1934_, v___x_1935_);
v___x_1937_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_1938_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__77, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__77_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__77);
v___x_1939_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__79));
lean_inc_n(v_currMacroScope_1933_, 3);
lean_inc_n(v_quotContext_1932_, 3);
v___x_1940_ = l_Lean_addMacroScope(v_quotContext_1932_, v___x_1939_, v_currMacroScope_1933_);
v___x_1941_ = lean_box(0);
v___x_1942_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__83));
lean_inc_n(v___x_1936_, 13);
v___x_1943_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1943_, 0, v___x_1936_);
lean_ctor_set(v___x_1943_, 1, v___x_1938_);
lean_ctor_set(v___x_1943_, 2, v___x_1940_);
lean_ctor_set(v___x_1943_, 3, v___x_1942_);
v___x_1944_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_1945_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__42));
v___x_1946_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__44));
v___x_1947_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__45));
v___x_1948_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1948_, 0, v___x_1936_);
lean_ctor_set(v___x_1948_, 1, v___x_1947_);
v___x_1949_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__47));
v___x_1950_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49);
v___x_1951_ = lean_box(0);
v___x_1952_ = l_Lean_addMacroScope(v_quotContext_1932_, v___x_1951_, v_currMacroScope_1933_);
v___x_1953_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__65));
v___x_1954_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1954_, 0, v___x_1936_);
lean_ctor_set(v___x_1954_, 1, v___x_1950_);
lean_ctor_set(v___x_1954_, 2, v___x_1952_);
lean_ctor_set(v___x_1954_, 3, v___x_1953_);
v___x_1955_ = l_Lean_Syntax_node1(v___x_1936_, v___x_1949_, v___x_1954_);
v___x_1956_ = l_Lean_Syntax_node2(v___x_1936_, v___x_1946_, v___x_1948_, v___x_1955_);
v___x_1957_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__67));
v___x_1958_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__68));
v___x_1959_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1959_, 0, v___x_1936_);
lean_ctor_set(v___x_1959_, 1, v___x_1958_);
v___x_1960_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__70, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__70_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__70);
v___x_1961_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__71));
v___x_1962_ = l_Lean_addMacroScope(v_quotContext_1932_, v___x_1961_, v_currMacroScope_1933_);
v___x_1963_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1963_, 0, v___x_1936_);
lean_ctor_set(v___x_1963_, 1, v___x_1960_);
lean_ctor_set(v___x_1963_, 2, v___x_1962_);
lean_ctor_set(v___x_1963_, 3, v___x_1941_);
v___x_1964_ = l_Lean_Syntax_node2(v___x_1936_, v___x_1957_, v___x_1959_, v___x_1963_);
v___x_1965_ = l_Lean_Syntax_node1(v___x_1936_, v___x_1944_, v_a_1927_);
v___x_1966_ = l_Lean_Syntax_node2(v___x_1936_, v___x_1937_, v___x_1964_, v___x_1965_);
v___x_1967_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__72));
v___x_1968_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1968_, 0, v___x_1936_);
lean_ctor_set(v___x_1968_, 1, v___x_1967_);
v___x_1969_ = l_Lean_Syntax_node3(v___x_1936_, v___x_1945_, v___x_1956_, v___x_1966_, v___x_1968_);
v___x_1970_ = l_Lean_Syntax_node1(v___x_1936_, v___x_1944_, v___x_1969_);
v___x_1971_ = l_Lean_Syntax_node2(v___x_1936_, v___x_1937_, v___x_1943_, v___x_1970_);
if (v_isShared_1931_ == 0)
{
lean_ctor_set(v___x_1930_, 0, v___x_1971_);
v___x_1973_ = v___x_1930_;
goto v_reusejp_1972_;
}
else
{
lean_object* v_reuseFailAlloc_1974_; 
v_reuseFailAlloc_1974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1974_, 0, v___x_1971_);
lean_ctor_set(v_reuseFailAlloc_1974_, 1, v_a_1928_);
v___x_1973_ = v_reuseFailAlloc_1974_;
goto v_reusejp_1972_;
}
v_reusejp_1972_:
{
return v___x_1973_;
}
}
}
else
{
lean_object* v_val_1976_; uint8_t v___x_1977_; lean_object* v___x_1978_; lean_object* v_a_1979_; lean_object* v_a_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_2027_; 
v_val_1976_ = lean_ctor_get(v_presentation_1924_, 0);
lean_inc(v_val_1976_);
lean_dec_ref_known(v_presentation_1924_, 1);
v___x_1977_ = lean_unbox(v_val_1976_);
lean_dec(v_val_1976_);
v___x_1978_ = l___private_Std_Time_Notation_0__Std_Time_convertText(v___x_1977_, v_a_1718_, v_a_1719_);
v_a_1979_ = lean_ctor_get(v___x_1978_, 0);
v_a_1980_ = lean_ctor_get(v___x_1978_, 1);
v_isSharedCheck_2027_ = !lean_is_exclusive(v___x_1978_);
if (v_isSharedCheck_2027_ == 0)
{
v___x_1982_ = v___x_1978_;
v_isShared_1983_ = v_isSharedCheck_2027_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_a_1980_);
lean_inc(v_a_1979_);
lean_dec(v___x_1978_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_2027_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v_quotContext_1984_; lean_object* v_currMacroScope_1985_; lean_object* v_ref_1986_; uint8_t v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2025_; 
v_quotContext_1984_ = lean_ctor_get(v_a_1718_, 1);
v_currMacroScope_1985_ = lean_ctor_get(v_a_1718_, 2);
v_ref_1986_ = lean_ctor_get(v_a_1718_, 5);
v___x_1987_ = 0;
v___x_1988_ = l_Lean_SourceInfo_fromRef(v_ref_1986_, v___x_1987_);
v___x_1989_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_1990_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__77, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__77_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__77);
v___x_1991_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__79));
lean_inc_n(v_currMacroScope_1985_, 3);
lean_inc_n(v_quotContext_1984_, 3);
v___x_1992_ = l_Lean_addMacroScope(v_quotContext_1984_, v___x_1991_, v_currMacroScope_1985_);
v___x_1993_ = lean_box(0);
v___x_1994_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__83));
lean_inc_n(v___x_1988_, 13);
v___x_1995_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1995_, 0, v___x_1988_);
lean_ctor_set(v___x_1995_, 1, v___x_1990_);
lean_ctor_set(v___x_1995_, 2, v___x_1992_);
lean_ctor_set(v___x_1995_, 3, v___x_1994_);
v___x_1996_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_1997_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__42));
v___x_1998_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__44));
v___x_1999_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__45));
v___x_2000_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2000_, 0, v___x_1988_);
lean_ctor_set(v___x_2000_, 1, v___x_1999_);
v___x_2001_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__47));
v___x_2002_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49);
v___x_2003_ = lean_box(0);
v___x_2004_ = l_Lean_addMacroScope(v_quotContext_1984_, v___x_2003_, v_currMacroScope_1985_);
v___x_2005_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__65));
v___x_2006_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2006_, 0, v___x_1988_);
lean_ctor_set(v___x_2006_, 1, v___x_2002_);
lean_ctor_set(v___x_2006_, 2, v___x_2004_);
lean_ctor_set(v___x_2006_, 3, v___x_2005_);
v___x_2007_ = l_Lean_Syntax_node1(v___x_1988_, v___x_2001_, v___x_2006_);
v___x_2008_ = l_Lean_Syntax_node2(v___x_1988_, v___x_1998_, v___x_2000_, v___x_2007_);
v___x_2009_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__67));
v___x_2010_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__68));
v___x_2011_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2011_, 0, v___x_1988_);
lean_ctor_set(v___x_2011_, 1, v___x_2010_);
v___x_2012_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__74, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__74_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__74);
v___x_2013_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__75));
v___x_2014_ = l_Lean_addMacroScope(v_quotContext_1984_, v___x_2013_, v_currMacroScope_1985_);
v___x_2015_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2015_, 0, v___x_1988_);
lean_ctor_set(v___x_2015_, 1, v___x_2012_);
lean_ctor_set(v___x_2015_, 2, v___x_2014_);
lean_ctor_set(v___x_2015_, 3, v___x_1993_);
v___x_2016_ = l_Lean_Syntax_node2(v___x_1988_, v___x_2009_, v___x_2011_, v___x_2015_);
v___x_2017_ = l_Lean_Syntax_node1(v___x_1988_, v___x_1996_, v_a_1979_);
v___x_2018_ = l_Lean_Syntax_node2(v___x_1988_, v___x_1989_, v___x_2016_, v___x_2017_);
v___x_2019_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__72));
v___x_2020_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2020_, 0, v___x_1988_);
lean_ctor_set(v___x_2020_, 1, v___x_2019_);
v___x_2021_ = l_Lean_Syntax_node3(v___x_1988_, v___x_1997_, v___x_2008_, v___x_2018_, v___x_2020_);
v___x_2022_ = l_Lean_Syntax_node1(v___x_1988_, v___x_1996_, v___x_2021_);
v___x_2023_ = l_Lean_Syntax_node2(v___x_1988_, v___x_1989_, v___x_1995_, v___x_2022_);
if (v_isShared_1983_ == 0)
{
lean_ctor_set(v___x_1982_, 0, v___x_2023_);
v___x_2025_ = v___x_1982_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v___x_2023_);
lean_ctor_set(v_reuseFailAlloc_2026_, 1, v_a_1980_);
v___x_2025_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
return v___x_2025_;
}
}
}
}
case 6:
{
lean_object* v_presentation_2028_; lean_object* v___x_2029_; lean_object* v_a_2030_; lean_object* v_a_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2052_; 
v_presentation_2028_ = lean_ctor_get(v_x_1717_, 0);
lean_inc(v_presentation_2028_);
lean_dec_ref_known(v_x_1717_, 1);
v___x_2029_ = l___private_Std_Time_Notation_0__Std_Time_convertNumber(v_presentation_2028_, v_a_1718_, v_a_1719_);
v_a_2030_ = lean_ctor_get(v___x_2029_, 0);
v_a_2031_ = lean_ctor_get(v___x_2029_, 1);
v_isSharedCheck_2052_ = !lean_is_exclusive(v___x_2029_);
if (v_isSharedCheck_2052_ == 0)
{
v___x_2033_ = v___x_2029_;
v_isShared_2034_ = v_isSharedCheck_2052_;
goto v_resetjp_2032_;
}
else
{
lean_inc(v_a_2031_);
lean_inc(v_a_2030_);
lean_dec(v___x_2029_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2052_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
lean_object* v_quotContext_2035_; lean_object* v_currMacroScope_2036_; lean_object* v_ref_2037_; uint8_t v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2050_; 
v_quotContext_2035_ = lean_ctor_get(v_a_1718_, 1);
v_currMacroScope_2036_ = lean_ctor_get(v_a_1718_, 2);
v_ref_2037_ = lean_ctor_get(v_a_1718_, 5);
v___x_2038_ = 0;
v___x_2039_ = l_Lean_SourceInfo_fromRef(v_ref_2037_, v___x_2038_);
v___x_2040_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2041_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__85, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__85_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__85);
v___x_2042_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__87));
lean_inc(v_currMacroScope_2036_);
lean_inc(v_quotContext_2035_);
v___x_2043_ = l_Lean_addMacroScope(v_quotContext_2035_, v___x_2042_, v_currMacroScope_2036_);
v___x_2044_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__91));
lean_inc_n(v___x_2039_, 2);
v___x_2045_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2045_, 0, v___x_2039_);
lean_ctor_set(v___x_2045_, 1, v___x_2041_);
lean_ctor_set(v___x_2045_, 2, v___x_2043_);
lean_ctor_set(v___x_2045_, 3, v___x_2044_);
v___x_2046_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2047_ = l_Lean_Syntax_node1(v___x_2039_, v___x_2046_, v_a_2030_);
v___x_2048_ = l_Lean_Syntax_node2(v___x_2039_, v___x_2040_, v___x_2045_, v___x_2047_);
if (v_isShared_2034_ == 0)
{
lean_ctor_set(v___x_2033_, 0, v___x_2048_);
v___x_2050_ = v___x_2033_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v___x_2048_);
lean_ctor_set(v_reuseFailAlloc_2051_, 1, v_a_2031_);
v___x_2050_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
return v___x_2050_;
}
}
}
case 7:
{
lean_object* v_presentation_2053_; 
v_presentation_2053_ = lean_ctor_get(v_x_1717_, 0);
lean_inc_ref(v_presentation_2053_);
lean_dec_ref_known(v_x_1717_, 1);
if (lean_obj_tag(v_presentation_2053_) == 0)
{
lean_object* v_val_2054_; lean_object* v___x_2055_; lean_object* v_a_2056_; lean_object* v_a_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2104_; 
v_val_2054_ = lean_ctor_get(v_presentation_2053_, 0);
lean_inc(v_val_2054_);
lean_dec_ref_known(v_presentation_2053_, 1);
v___x_2055_ = l___private_Std_Time_Notation_0__Std_Time_convertNumber(v_val_2054_, v_a_1718_, v_a_1719_);
v_a_2056_ = lean_ctor_get(v___x_2055_, 0);
v_a_2057_ = lean_ctor_get(v___x_2055_, 1);
v_isSharedCheck_2104_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_2059_ = v___x_2055_;
v_isShared_2060_ = v_isSharedCheck_2104_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_a_2057_);
lean_inc(v_a_2056_);
lean_dec(v___x_2055_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2104_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v_quotContext_2061_; lean_object* v_currMacroScope_2062_; lean_object* v_ref_2063_; uint8_t v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2102_; 
v_quotContext_2061_ = lean_ctor_get(v_a_1718_, 1);
v_currMacroScope_2062_ = lean_ctor_get(v_a_1718_, 2);
v_ref_2063_ = lean_ctor_get(v_a_1718_, 5);
v___x_2064_ = 0;
v___x_2065_ = l_Lean_SourceInfo_fromRef(v_ref_2063_, v___x_2064_);
v___x_2066_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2067_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__93, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__93_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__93);
v___x_2068_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__95));
lean_inc_n(v_currMacroScope_2062_, 3);
lean_inc_n(v_quotContext_2061_, 3);
v___x_2069_ = l_Lean_addMacroScope(v_quotContext_2061_, v___x_2068_, v_currMacroScope_2062_);
v___x_2070_ = lean_box(0);
v___x_2071_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__99));
lean_inc_n(v___x_2065_, 13);
v___x_2072_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2072_, 0, v___x_2065_);
lean_ctor_set(v___x_2072_, 1, v___x_2067_);
lean_ctor_set(v___x_2072_, 2, v___x_2069_);
lean_ctor_set(v___x_2072_, 3, v___x_2071_);
v___x_2073_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2074_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__42));
v___x_2075_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__44));
v___x_2076_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__45));
v___x_2077_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2077_, 0, v___x_2065_);
lean_ctor_set(v___x_2077_, 1, v___x_2076_);
v___x_2078_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__47));
v___x_2079_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49);
v___x_2080_ = lean_box(0);
v___x_2081_ = l_Lean_addMacroScope(v_quotContext_2061_, v___x_2080_, v_currMacroScope_2062_);
v___x_2082_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__65));
v___x_2083_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2083_, 0, v___x_2065_);
lean_ctor_set(v___x_2083_, 1, v___x_2079_);
lean_ctor_set(v___x_2083_, 2, v___x_2081_);
lean_ctor_set(v___x_2083_, 3, v___x_2082_);
v___x_2084_ = l_Lean_Syntax_node1(v___x_2065_, v___x_2078_, v___x_2083_);
v___x_2085_ = l_Lean_Syntax_node2(v___x_2065_, v___x_2075_, v___x_2077_, v___x_2084_);
v___x_2086_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__67));
v___x_2087_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__68));
v___x_2088_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2088_, 0, v___x_2065_);
lean_ctor_set(v___x_2088_, 1, v___x_2087_);
v___x_2089_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__70, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__70_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__70);
v___x_2090_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__71));
v___x_2091_ = l_Lean_addMacroScope(v_quotContext_2061_, v___x_2090_, v_currMacroScope_2062_);
v___x_2092_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2092_, 0, v___x_2065_);
lean_ctor_set(v___x_2092_, 1, v___x_2089_);
lean_ctor_set(v___x_2092_, 2, v___x_2091_);
lean_ctor_set(v___x_2092_, 3, v___x_2070_);
v___x_2093_ = l_Lean_Syntax_node2(v___x_2065_, v___x_2086_, v___x_2088_, v___x_2092_);
v___x_2094_ = l_Lean_Syntax_node1(v___x_2065_, v___x_2073_, v_a_2056_);
v___x_2095_ = l_Lean_Syntax_node2(v___x_2065_, v___x_2066_, v___x_2093_, v___x_2094_);
v___x_2096_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__72));
v___x_2097_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2097_, 0, v___x_2065_);
lean_ctor_set(v___x_2097_, 1, v___x_2096_);
v___x_2098_ = l_Lean_Syntax_node3(v___x_2065_, v___x_2074_, v___x_2085_, v___x_2095_, v___x_2097_);
v___x_2099_ = l_Lean_Syntax_node1(v___x_2065_, v___x_2073_, v___x_2098_);
v___x_2100_ = l_Lean_Syntax_node2(v___x_2065_, v___x_2066_, v___x_2072_, v___x_2099_);
if (v_isShared_2060_ == 0)
{
lean_ctor_set(v___x_2059_, 0, v___x_2100_);
v___x_2102_ = v___x_2059_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v___x_2100_);
lean_ctor_set(v_reuseFailAlloc_2103_, 1, v_a_2057_);
v___x_2102_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
return v___x_2102_;
}
}
}
else
{
lean_object* v_val_2105_; uint8_t v___x_2106_; lean_object* v___x_2107_; lean_object* v_a_2108_; lean_object* v_a_2109_; lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2156_; 
v_val_2105_ = lean_ctor_get(v_presentation_2053_, 0);
lean_inc(v_val_2105_);
lean_dec_ref_known(v_presentation_2053_, 1);
v___x_2106_ = lean_unbox(v_val_2105_);
lean_dec(v_val_2105_);
v___x_2107_ = l___private_Std_Time_Notation_0__Std_Time_convertText(v___x_2106_, v_a_1718_, v_a_1719_);
v_a_2108_ = lean_ctor_get(v___x_2107_, 0);
v_a_2109_ = lean_ctor_get(v___x_2107_, 1);
v_isSharedCheck_2156_ = !lean_is_exclusive(v___x_2107_);
if (v_isSharedCheck_2156_ == 0)
{
v___x_2111_ = v___x_2107_;
v_isShared_2112_ = v_isSharedCheck_2156_;
goto v_resetjp_2110_;
}
else
{
lean_inc(v_a_2109_);
lean_inc(v_a_2108_);
lean_dec(v___x_2107_);
v___x_2111_ = lean_box(0);
v_isShared_2112_ = v_isSharedCheck_2156_;
goto v_resetjp_2110_;
}
v_resetjp_2110_:
{
lean_object* v_quotContext_2113_; lean_object* v_currMacroScope_2114_; lean_object* v_ref_2115_; uint8_t v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2154_; 
v_quotContext_2113_ = lean_ctor_get(v_a_1718_, 1);
v_currMacroScope_2114_ = lean_ctor_get(v_a_1718_, 2);
v_ref_2115_ = lean_ctor_get(v_a_1718_, 5);
v___x_2116_ = 0;
v___x_2117_ = l_Lean_SourceInfo_fromRef(v_ref_2115_, v___x_2116_);
v___x_2118_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2119_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__93, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__93_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__93);
v___x_2120_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__95));
lean_inc_n(v_currMacroScope_2114_, 3);
lean_inc_n(v_quotContext_2113_, 3);
v___x_2121_ = l_Lean_addMacroScope(v_quotContext_2113_, v___x_2120_, v_currMacroScope_2114_);
v___x_2122_ = lean_box(0);
v___x_2123_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__99));
lean_inc_n(v___x_2117_, 13);
v___x_2124_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2124_, 0, v___x_2117_);
lean_ctor_set(v___x_2124_, 1, v___x_2119_);
lean_ctor_set(v___x_2124_, 2, v___x_2121_);
lean_ctor_set(v___x_2124_, 3, v___x_2123_);
v___x_2125_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2126_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__42));
v___x_2127_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__44));
v___x_2128_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__45));
v___x_2129_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2129_, 0, v___x_2117_);
lean_ctor_set(v___x_2129_, 1, v___x_2128_);
v___x_2130_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__47));
v___x_2131_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49);
v___x_2132_ = lean_box(0);
v___x_2133_ = l_Lean_addMacroScope(v_quotContext_2113_, v___x_2132_, v_currMacroScope_2114_);
v___x_2134_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__65));
v___x_2135_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2135_, 0, v___x_2117_);
lean_ctor_set(v___x_2135_, 1, v___x_2131_);
lean_ctor_set(v___x_2135_, 2, v___x_2133_);
lean_ctor_set(v___x_2135_, 3, v___x_2134_);
v___x_2136_ = l_Lean_Syntax_node1(v___x_2117_, v___x_2130_, v___x_2135_);
v___x_2137_ = l_Lean_Syntax_node2(v___x_2117_, v___x_2127_, v___x_2129_, v___x_2136_);
v___x_2138_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__67));
v___x_2139_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__68));
v___x_2140_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2140_, 0, v___x_2117_);
lean_ctor_set(v___x_2140_, 1, v___x_2139_);
v___x_2141_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__74, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__74_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__74);
v___x_2142_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__75));
v___x_2143_ = l_Lean_addMacroScope(v_quotContext_2113_, v___x_2142_, v_currMacroScope_2114_);
v___x_2144_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2144_, 0, v___x_2117_);
lean_ctor_set(v___x_2144_, 1, v___x_2141_);
lean_ctor_set(v___x_2144_, 2, v___x_2143_);
lean_ctor_set(v___x_2144_, 3, v___x_2122_);
v___x_2145_ = l_Lean_Syntax_node2(v___x_2117_, v___x_2138_, v___x_2140_, v___x_2144_);
v___x_2146_ = l_Lean_Syntax_node1(v___x_2117_, v___x_2125_, v_a_2108_);
v___x_2147_ = l_Lean_Syntax_node2(v___x_2117_, v___x_2118_, v___x_2145_, v___x_2146_);
v___x_2148_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__72));
v___x_2149_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2149_, 0, v___x_2117_);
lean_ctor_set(v___x_2149_, 1, v___x_2148_);
v___x_2150_ = l_Lean_Syntax_node3(v___x_2117_, v___x_2126_, v___x_2137_, v___x_2147_, v___x_2149_);
v___x_2151_ = l_Lean_Syntax_node1(v___x_2117_, v___x_2125_, v___x_2150_);
v___x_2152_ = l_Lean_Syntax_node2(v___x_2117_, v___x_2118_, v___x_2124_, v___x_2151_);
if (v_isShared_2112_ == 0)
{
lean_ctor_set(v___x_2111_, 0, v___x_2152_);
v___x_2154_ = v___x_2111_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v___x_2152_);
lean_ctor_set(v_reuseFailAlloc_2155_, 1, v_a_2109_);
v___x_2154_ = v_reuseFailAlloc_2155_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
return v___x_2154_;
}
}
}
}
case 8:
{
lean_object* v_presentation_2157_; 
v_presentation_2157_ = lean_ctor_get(v_x_1717_, 0);
lean_inc_ref(v_presentation_2157_);
lean_dec_ref_known(v_x_1717_, 1);
if (lean_obj_tag(v_presentation_2157_) == 0)
{
lean_object* v_val_2158_; lean_object* v___x_2159_; lean_object* v_a_2160_; lean_object* v_a_2161_; lean_object* v___x_2163_; uint8_t v_isShared_2164_; uint8_t v_isSharedCheck_2208_; 
v_val_2158_ = lean_ctor_get(v_presentation_2157_, 0);
lean_inc(v_val_2158_);
lean_dec_ref_known(v_presentation_2157_, 1);
v___x_2159_ = l___private_Std_Time_Notation_0__Std_Time_convertNumber(v_val_2158_, v_a_1718_, v_a_1719_);
v_a_2160_ = lean_ctor_get(v___x_2159_, 0);
v_a_2161_ = lean_ctor_get(v___x_2159_, 1);
v_isSharedCheck_2208_ = !lean_is_exclusive(v___x_2159_);
if (v_isSharedCheck_2208_ == 0)
{
v___x_2163_ = v___x_2159_;
v_isShared_2164_ = v_isSharedCheck_2208_;
goto v_resetjp_2162_;
}
else
{
lean_inc(v_a_2161_);
lean_inc(v_a_2160_);
lean_dec(v___x_2159_);
v___x_2163_ = lean_box(0);
v_isShared_2164_ = v_isSharedCheck_2208_;
goto v_resetjp_2162_;
}
v_resetjp_2162_:
{
lean_object* v_quotContext_2165_; lean_object* v_currMacroScope_2166_; lean_object* v_ref_2167_; uint8_t v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2206_; 
v_quotContext_2165_ = lean_ctor_get(v_a_1718_, 1);
v_currMacroScope_2166_ = lean_ctor_get(v_a_1718_, 2);
v_ref_2167_ = lean_ctor_get(v_a_1718_, 5);
v___x_2168_ = 0;
v___x_2169_ = l_Lean_SourceInfo_fromRef(v_ref_2167_, v___x_2168_);
v___x_2170_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2171_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__101, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__101_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__101);
v___x_2172_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__103));
lean_inc_n(v_currMacroScope_2166_, 3);
lean_inc_n(v_quotContext_2165_, 3);
v___x_2173_ = l_Lean_addMacroScope(v_quotContext_2165_, v___x_2172_, v_currMacroScope_2166_);
v___x_2174_ = lean_box(0);
v___x_2175_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__107));
lean_inc_n(v___x_2169_, 13);
v___x_2176_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2176_, 0, v___x_2169_);
lean_ctor_set(v___x_2176_, 1, v___x_2171_);
lean_ctor_set(v___x_2176_, 2, v___x_2173_);
lean_ctor_set(v___x_2176_, 3, v___x_2175_);
v___x_2177_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2178_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__42));
v___x_2179_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__44));
v___x_2180_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__45));
v___x_2181_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2181_, 0, v___x_2169_);
lean_ctor_set(v___x_2181_, 1, v___x_2180_);
v___x_2182_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__47));
v___x_2183_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49);
v___x_2184_ = lean_box(0);
v___x_2185_ = l_Lean_addMacroScope(v_quotContext_2165_, v___x_2184_, v_currMacroScope_2166_);
v___x_2186_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__65));
v___x_2187_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2187_, 0, v___x_2169_);
lean_ctor_set(v___x_2187_, 1, v___x_2183_);
lean_ctor_set(v___x_2187_, 2, v___x_2185_);
lean_ctor_set(v___x_2187_, 3, v___x_2186_);
v___x_2188_ = l_Lean_Syntax_node1(v___x_2169_, v___x_2182_, v___x_2187_);
v___x_2189_ = l_Lean_Syntax_node2(v___x_2169_, v___x_2179_, v___x_2181_, v___x_2188_);
v___x_2190_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__67));
v___x_2191_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__68));
v___x_2192_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2192_, 0, v___x_2169_);
lean_ctor_set(v___x_2192_, 1, v___x_2191_);
v___x_2193_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__70, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__70_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__70);
v___x_2194_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__71));
v___x_2195_ = l_Lean_addMacroScope(v_quotContext_2165_, v___x_2194_, v_currMacroScope_2166_);
v___x_2196_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2196_, 0, v___x_2169_);
lean_ctor_set(v___x_2196_, 1, v___x_2193_);
lean_ctor_set(v___x_2196_, 2, v___x_2195_);
lean_ctor_set(v___x_2196_, 3, v___x_2174_);
v___x_2197_ = l_Lean_Syntax_node2(v___x_2169_, v___x_2190_, v___x_2192_, v___x_2196_);
v___x_2198_ = l_Lean_Syntax_node1(v___x_2169_, v___x_2177_, v_a_2160_);
v___x_2199_ = l_Lean_Syntax_node2(v___x_2169_, v___x_2170_, v___x_2197_, v___x_2198_);
v___x_2200_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__72));
v___x_2201_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2201_, 0, v___x_2169_);
lean_ctor_set(v___x_2201_, 1, v___x_2200_);
v___x_2202_ = l_Lean_Syntax_node3(v___x_2169_, v___x_2178_, v___x_2189_, v___x_2199_, v___x_2201_);
v___x_2203_ = l_Lean_Syntax_node1(v___x_2169_, v___x_2177_, v___x_2202_);
v___x_2204_ = l_Lean_Syntax_node2(v___x_2169_, v___x_2170_, v___x_2176_, v___x_2203_);
if (v_isShared_2164_ == 0)
{
lean_ctor_set(v___x_2163_, 0, v___x_2204_);
v___x_2206_ = v___x_2163_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2207_; 
v_reuseFailAlloc_2207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2207_, 0, v___x_2204_);
lean_ctor_set(v_reuseFailAlloc_2207_, 1, v_a_2161_);
v___x_2206_ = v_reuseFailAlloc_2207_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
return v___x_2206_;
}
}
}
else
{
lean_object* v_val_2209_; uint8_t v___x_2210_; lean_object* v___x_2211_; lean_object* v_a_2212_; lean_object* v_a_2213_; lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2260_; 
v_val_2209_ = lean_ctor_get(v_presentation_2157_, 0);
lean_inc(v_val_2209_);
lean_dec_ref_known(v_presentation_2157_, 1);
v___x_2210_ = lean_unbox(v_val_2209_);
lean_dec(v_val_2209_);
v___x_2211_ = l___private_Std_Time_Notation_0__Std_Time_convertText(v___x_2210_, v_a_1718_, v_a_1719_);
v_a_2212_ = lean_ctor_get(v___x_2211_, 0);
v_a_2213_ = lean_ctor_get(v___x_2211_, 1);
v_isSharedCheck_2260_ = !lean_is_exclusive(v___x_2211_);
if (v_isSharedCheck_2260_ == 0)
{
v___x_2215_ = v___x_2211_;
v_isShared_2216_ = v_isSharedCheck_2260_;
goto v_resetjp_2214_;
}
else
{
lean_inc(v_a_2213_);
lean_inc(v_a_2212_);
lean_dec(v___x_2211_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2260_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
lean_object* v_quotContext_2217_; lean_object* v_currMacroScope_2218_; lean_object* v_ref_2219_; uint8_t v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2258_; 
v_quotContext_2217_ = lean_ctor_get(v_a_1718_, 1);
v_currMacroScope_2218_ = lean_ctor_get(v_a_1718_, 2);
v_ref_2219_ = lean_ctor_get(v_a_1718_, 5);
v___x_2220_ = 0;
v___x_2221_ = l_Lean_SourceInfo_fromRef(v_ref_2219_, v___x_2220_);
v___x_2222_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2223_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__101, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__101_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__101);
v___x_2224_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__103));
lean_inc_n(v_currMacroScope_2218_, 3);
lean_inc_n(v_quotContext_2217_, 3);
v___x_2225_ = l_Lean_addMacroScope(v_quotContext_2217_, v___x_2224_, v_currMacroScope_2218_);
v___x_2226_ = lean_box(0);
v___x_2227_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__107));
lean_inc_n(v___x_2221_, 13);
v___x_2228_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2228_, 0, v___x_2221_);
lean_ctor_set(v___x_2228_, 1, v___x_2223_);
lean_ctor_set(v___x_2228_, 2, v___x_2225_);
lean_ctor_set(v___x_2228_, 3, v___x_2227_);
v___x_2229_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2230_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__42));
v___x_2231_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__44));
v___x_2232_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__45));
v___x_2233_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2233_, 0, v___x_2221_);
lean_ctor_set(v___x_2233_, 1, v___x_2232_);
v___x_2234_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__47));
v___x_2235_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49);
v___x_2236_ = lean_box(0);
v___x_2237_ = l_Lean_addMacroScope(v_quotContext_2217_, v___x_2236_, v_currMacroScope_2218_);
v___x_2238_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__65));
v___x_2239_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2239_, 0, v___x_2221_);
lean_ctor_set(v___x_2239_, 1, v___x_2235_);
lean_ctor_set(v___x_2239_, 2, v___x_2237_);
lean_ctor_set(v___x_2239_, 3, v___x_2238_);
v___x_2240_ = l_Lean_Syntax_node1(v___x_2221_, v___x_2234_, v___x_2239_);
v___x_2241_ = l_Lean_Syntax_node2(v___x_2221_, v___x_2231_, v___x_2233_, v___x_2240_);
v___x_2242_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__67));
v___x_2243_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__68));
v___x_2244_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2244_, 0, v___x_2221_);
lean_ctor_set(v___x_2244_, 1, v___x_2243_);
v___x_2245_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__74, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__74_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__74);
v___x_2246_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__75));
v___x_2247_ = l_Lean_addMacroScope(v_quotContext_2217_, v___x_2246_, v_currMacroScope_2218_);
v___x_2248_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2248_, 0, v___x_2221_);
lean_ctor_set(v___x_2248_, 1, v___x_2245_);
lean_ctor_set(v___x_2248_, 2, v___x_2247_);
lean_ctor_set(v___x_2248_, 3, v___x_2226_);
v___x_2249_ = l_Lean_Syntax_node2(v___x_2221_, v___x_2242_, v___x_2244_, v___x_2248_);
v___x_2250_ = l_Lean_Syntax_node1(v___x_2221_, v___x_2229_, v_a_2212_);
v___x_2251_ = l_Lean_Syntax_node2(v___x_2221_, v___x_2222_, v___x_2249_, v___x_2250_);
v___x_2252_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__72));
v___x_2253_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2253_, 0, v___x_2221_);
lean_ctor_set(v___x_2253_, 1, v___x_2252_);
v___x_2254_ = l_Lean_Syntax_node3(v___x_2221_, v___x_2230_, v___x_2241_, v___x_2251_, v___x_2253_);
v___x_2255_ = l_Lean_Syntax_node1(v___x_2221_, v___x_2229_, v___x_2254_);
v___x_2256_ = l_Lean_Syntax_node2(v___x_2221_, v___x_2222_, v___x_2228_, v___x_2255_);
if (v_isShared_2216_ == 0)
{
lean_ctor_set(v___x_2215_, 0, v___x_2256_);
v___x_2258_ = v___x_2215_;
goto v_reusejp_2257_;
}
else
{
lean_object* v_reuseFailAlloc_2259_; 
v_reuseFailAlloc_2259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2259_, 0, v___x_2256_);
lean_ctor_set(v_reuseFailAlloc_2259_, 1, v_a_2213_);
v___x_2258_ = v_reuseFailAlloc_2259_;
goto v_reusejp_2257_;
}
v_reusejp_2257_:
{
return v___x_2258_;
}
}
}
}
case 9:
{
lean_object* v_presentation_2261_; lean_object* v___x_2262_; lean_object* v_a_2263_; lean_object* v_a_2264_; lean_object* v___x_2266_; uint8_t v_isShared_2267_; uint8_t v_isSharedCheck_2285_; 
v_presentation_2261_ = lean_ctor_get(v_x_1717_, 0);
lean_inc(v_presentation_2261_);
lean_dec_ref_known(v_x_1717_, 1);
v___x_2262_ = l___private_Std_Time_Notation_0__Std_Time_convertYear(v_presentation_2261_, v_a_1718_, v_a_1719_);
v_a_2263_ = lean_ctor_get(v___x_2262_, 0);
v_a_2264_ = lean_ctor_get(v___x_2262_, 1);
v_isSharedCheck_2285_ = !lean_is_exclusive(v___x_2262_);
if (v_isSharedCheck_2285_ == 0)
{
v___x_2266_ = v___x_2262_;
v_isShared_2267_ = v_isSharedCheck_2285_;
goto v_resetjp_2265_;
}
else
{
lean_inc(v_a_2264_);
lean_inc(v_a_2263_);
lean_dec(v___x_2262_);
v___x_2266_ = lean_box(0);
v_isShared_2267_ = v_isSharedCheck_2285_;
goto v_resetjp_2265_;
}
v_resetjp_2265_:
{
lean_object* v_quotContext_2268_; lean_object* v_currMacroScope_2269_; lean_object* v_ref_2270_; uint8_t v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2283_; 
v_quotContext_2268_ = lean_ctor_get(v_a_1718_, 1);
v_currMacroScope_2269_ = lean_ctor_get(v_a_1718_, 2);
v_ref_2270_ = lean_ctor_get(v_a_1718_, 5);
v___x_2271_ = 0;
v___x_2272_ = l_Lean_SourceInfo_fromRef(v_ref_2270_, v___x_2271_);
v___x_2273_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2274_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__109, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__109_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__109);
v___x_2275_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__111));
lean_inc(v_currMacroScope_2269_);
lean_inc(v_quotContext_2268_);
v___x_2276_ = l_Lean_addMacroScope(v_quotContext_2268_, v___x_2275_, v_currMacroScope_2269_);
v___x_2277_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__115));
lean_inc_n(v___x_2272_, 2);
v___x_2278_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2278_, 0, v___x_2272_);
lean_ctor_set(v___x_2278_, 1, v___x_2274_);
lean_ctor_set(v___x_2278_, 2, v___x_2276_);
lean_ctor_set(v___x_2278_, 3, v___x_2277_);
v___x_2279_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2280_ = l_Lean_Syntax_node1(v___x_2272_, v___x_2279_, v_a_2263_);
v___x_2281_ = l_Lean_Syntax_node2(v___x_2272_, v___x_2273_, v___x_2278_, v___x_2280_);
if (v_isShared_2267_ == 0)
{
lean_ctor_set(v___x_2266_, 0, v___x_2281_);
v___x_2283_ = v___x_2266_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v___x_2281_);
lean_ctor_set(v_reuseFailAlloc_2284_, 1, v_a_2264_);
v___x_2283_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
return v___x_2283_;
}
}
}
case 10:
{
lean_object* v_presentation_2286_; lean_object* v___x_2287_; lean_object* v_a_2288_; lean_object* v_a_2289_; lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2310_; 
v_presentation_2286_ = lean_ctor_get(v_x_1717_, 0);
lean_inc(v_presentation_2286_);
lean_dec_ref_known(v_x_1717_, 1);
v___x_2287_ = l___private_Std_Time_Notation_0__Std_Time_convertNumber(v_presentation_2286_, v_a_1718_, v_a_1719_);
v_a_2288_ = lean_ctor_get(v___x_2287_, 0);
v_a_2289_ = lean_ctor_get(v___x_2287_, 1);
v_isSharedCheck_2310_ = !lean_is_exclusive(v___x_2287_);
if (v_isSharedCheck_2310_ == 0)
{
v___x_2291_ = v___x_2287_;
v_isShared_2292_ = v_isSharedCheck_2310_;
goto v_resetjp_2290_;
}
else
{
lean_inc(v_a_2289_);
lean_inc(v_a_2288_);
lean_dec(v___x_2287_);
v___x_2291_ = lean_box(0);
v_isShared_2292_ = v_isSharedCheck_2310_;
goto v_resetjp_2290_;
}
v_resetjp_2290_:
{
lean_object* v_quotContext_2293_; lean_object* v_currMacroScope_2294_; lean_object* v_ref_2295_; uint8_t v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2308_; 
v_quotContext_2293_ = lean_ctor_get(v_a_1718_, 1);
v_currMacroScope_2294_ = lean_ctor_get(v_a_1718_, 2);
v_ref_2295_ = lean_ctor_get(v_a_1718_, 5);
v___x_2296_ = 0;
v___x_2297_ = l_Lean_SourceInfo_fromRef(v_ref_2295_, v___x_2296_);
v___x_2298_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2299_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__117, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__117_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__117);
v___x_2300_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__119));
lean_inc(v_currMacroScope_2294_);
lean_inc(v_quotContext_2293_);
v___x_2301_ = l_Lean_addMacroScope(v_quotContext_2293_, v___x_2300_, v_currMacroScope_2294_);
v___x_2302_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__123));
lean_inc_n(v___x_2297_, 2);
v___x_2303_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2303_, 0, v___x_2297_);
lean_ctor_set(v___x_2303_, 1, v___x_2299_);
lean_ctor_set(v___x_2303_, 2, v___x_2301_);
lean_ctor_set(v___x_2303_, 3, v___x_2302_);
v___x_2304_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2305_ = l_Lean_Syntax_node1(v___x_2297_, v___x_2304_, v_a_2288_);
v___x_2306_ = l_Lean_Syntax_node2(v___x_2297_, v___x_2298_, v___x_2303_, v___x_2305_);
if (v_isShared_2292_ == 0)
{
lean_ctor_set(v___x_2291_, 0, v___x_2306_);
v___x_2308_ = v___x_2291_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v___x_2306_);
lean_ctor_set(v_reuseFailAlloc_2309_, 1, v_a_2289_);
v___x_2308_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
return v___x_2308_;
}
}
}
case 11:
{
lean_object* v_presentation_2311_; lean_object* v___x_2312_; lean_object* v_a_2313_; lean_object* v_a_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2335_; 
v_presentation_2311_ = lean_ctor_get(v_x_1717_, 0);
lean_inc(v_presentation_2311_);
lean_dec_ref_known(v_x_1717_, 1);
v___x_2312_ = l___private_Std_Time_Notation_0__Std_Time_convertNumber(v_presentation_2311_, v_a_1718_, v_a_1719_);
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
v_quotContext_2318_ = lean_ctor_get(v_a_1718_, 1);
v_currMacroScope_2319_ = lean_ctor_get(v_a_1718_, 2);
v_ref_2320_ = lean_ctor_get(v_a_1718_, 5);
v___x_2321_ = 0;
v___x_2322_ = l_Lean_SourceInfo_fromRef(v_ref_2320_, v___x_2321_);
v___x_2323_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2324_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__125, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__125_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__125);
v___x_2325_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__127));
lean_inc(v_currMacroScope_2319_);
lean_inc(v_quotContext_2318_);
v___x_2326_ = l_Lean_addMacroScope(v_quotContext_2318_, v___x_2325_, v_currMacroScope_2319_);
v___x_2327_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__131));
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
case 12:
{
uint8_t v_presentation_2336_; lean_object* v___x_2337_; lean_object* v_a_2338_; lean_object* v_a_2339_; lean_object* v___x_2341_; uint8_t v_isShared_2342_; uint8_t v_isSharedCheck_2360_; 
v_presentation_2336_ = lean_ctor_get_uint8(v_x_1717_, 0);
lean_dec_ref_known(v_x_1717_, 0);
v___x_2337_ = l___private_Std_Time_Notation_0__Std_Time_convertText(v_presentation_2336_, v_a_1718_, v_a_1719_);
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
v_quotContext_2343_ = lean_ctor_get(v_a_1718_, 1);
v_currMacroScope_2344_ = lean_ctor_get(v_a_1718_, 2);
v_ref_2345_ = lean_ctor_get(v_a_1718_, 5);
v___x_2346_ = 0;
v___x_2347_ = l_Lean_SourceInfo_fromRef(v_ref_2345_, v___x_2346_);
v___x_2348_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2349_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__133, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__133_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__133);
v___x_2350_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__135));
lean_inc(v_currMacroScope_2344_);
lean_inc(v_quotContext_2343_);
v___x_2351_ = l_Lean_addMacroScope(v_quotContext_2343_, v___x_2350_, v_currMacroScope_2344_);
v___x_2352_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__139));
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
case 13:
{
lean_object* v_presentation_2361_; 
v_presentation_2361_ = lean_ctor_get(v_x_1717_, 0);
lean_inc_ref(v_presentation_2361_);
lean_dec_ref_known(v_x_1717_, 1);
if (lean_obj_tag(v_presentation_2361_) == 0)
{
lean_object* v_val_2362_; lean_object* v___x_2363_; lean_object* v_a_2364_; lean_object* v_a_2365_; lean_object* v___x_2367_; uint8_t v_isShared_2368_; uint8_t v_isSharedCheck_2412_; 
v_val_2362_ = lean_ctor_get(v_presentation_2361_, 0);
lean_inc(v_val_2362_);
lean_dec_ref_known(v_presentation_2361_, 1);
v___x_2363_ = l___private_Std_Time_Notation_0__Std_Time_convertNumber(v_val_2362_, v_a_1718_, v_a_1719_);
v_a_2364_ = lean_ctor_get(v___x_2363_, 0);
v_a_2365_ = lean_ctor_get(v___x_2363_, 1);
v_isSharedCheck_2412_ = !lean_is_exclusive(v___x_2363_);
if (v_isSharedCheck_2412_ == 0)
{
v___x_2367_ = v___x_2363_;
v_isShared_2368_ = v_isSharedCheck_2412_;
goto v_resetjp_2366_;
}
else
{
lean_inc(v_a_2365_);
lean_inc(v_a_2364_);
lean_dec(v___x_2363_);
v___x_2367_ = lean_box(0);
v_isShared_2368_ = v_isSharedCheck_2412_;
goto v_resetjp_2366_;
}
v_resetjp_2366_:
{
lean_object* v_quotContext_2369_; lean_object* v_currMacroScope_2370_; lean_object* v_ref_2371_; uint8_t v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2410_; 
v_quotContext_2369_ = lean_ctor_get(v_a_1718_, 1);
v_currMacroScope_2370_ = lean_ctor_get(v_a_1718_, 2);
v_ref_2371_ = lean_ctor_get(v_a_1718_, 5);
v___x_2372_ = 0;
v___x_2373_ = l_Lean_SourceInfo_fromRef(v_ref_2371_, v___x_2372_);
v___x_2374_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2375_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__141, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__141_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__141);
v___x_2376_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__143));
lean_inc_n(v_currMacroScope_2370_, 3);
lean_inc_n(v_quotContext_2369_, 3);
v___x_2377_ = l_Lean_addMacroScope(v_quotContext_2369_, v___x_2376_, v_currMacroScope_2370_);
v___x_2378_ = lean_box(0);
v___x_2379_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__147));
lean_inc_n(v___x_2373_, 13);
v___x_2380_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2380_, 0, v___x_2373_);
lean_ctor_set(v___x_2380_, 1, v___x_2375_);
lean_ctor_set(v___x_2380_, 2, v___x_2377_);
lean_ctor_set(v___x_2380_, 3, v___x_2379_);
v___x_2381_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2382_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__42));
v___x_2383_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__44));
v___x_2384_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__45));
v___x_2385_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2385_, 0, v___x_2373_);
lean_ctor_set(v___x_2385_, 1, v___x_2384_);
v___x_2386_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__47));
v___x_2387_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49);
v___x_2388_ = lean_box(0);
v___x_2389_ = l_Lean_addMacroScope(v_quotContext_2369_, v___x_2388_, v_currMacroScope_2370_);
v___x_2390_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__65));
v___x_2391_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2391_, 0, v___x_2373_);
lean_ctor_set(v___x_2391_, 1, v___x_2387_);
lean_ctor_set(v___x_2391_, 2, v___x_2389_);
lean_ctor_set(v___x_2391_, 3, v___x_2390_);
v___x_2392_ = l_Lean_Syntax_node1(v___x_2373_, v___x_2386_, v___x_2391_);
v___x_2393_ = l_Lean_Syntax_node2(v___x_2373_, v___x_2383_, v___x_2385_, v___x_2392_);
v___x_2394_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__67));
v___x_2395_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__68));
v___x_2396_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2396_, 0, v___x_2373_);
lean_ctor_set(v___x_2396_, 1, v___x_2395_);
v___x_2397_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__70, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__70_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__70);
v___x_2398_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__71));
v___x_2399_ = l_Lean_addMacroScope(v_quotContext_2369_, v___x_2398_, v_currMacroScope_2370_);
v___x_2400_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2400_, 0, v___x_2373_);
lean_ctor_set(v___x_2400_, 1, v___x_2397_);
lean_ctor_set(v___x_2400_, 2, v___x_2399_);
lean_ctor_set(v___x_2400_, 3, v___x_2378_);
v___x_2401_ = l_Lean_Syntax_node2(v___x_2373_, v___x_2394_, v___x_2396_, v___x_2400_);
v___x_2402_ = l_Lean_Syntax_node1(v___x_2373_, v___x_2381_, v_a_2364_);
v___x_2403_ = l_Lean_Syntax_node2(v___x_2373_, v___x_2374_, v___x_2401_, v___x_2402_);
v___x_2404_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__72));
v___x_2405_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2405_, 0, v___x_2373_);
lean_ctor_set(v___x_2405_, 1, v___x_2404_);
v___x_2406_ = l_Lean_Syntax_node3(v___x_2373_, v___x_2382_, v___x_2393_, v___x_2403_, v___x_2405_);
v___x_2407_ = l_Lean_Syntax_node1(v___x_2373_, v___x_2381_, v___x_2406_);
v___x_2408_ = l_Lean_Syntax_node2(v___x_2373_, v___x_2374_, v___x_2380_, v___x_2407_);
if (v_isShared_2368_ == 0)
{
lean_ctor_set(v___x_2367_, 0, v___x_2408_);
v___x_2410_ = v___x_2367_;
goto v_reusejp_2409_;
}
else
{
lean_object* v_reuseFailAlloc_2411_; 
v_reuseFailAlloc_2411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2411_, 0, v___x_2408_);
lean_ctor_set(v_reuseFailAlloc_2411_, 1, v_a_2365_);
v___x_2410_ = v_reuseFailAlloc_2411_;
goto v_reusejp_2409_;
}
v_reusejp_2409_:
{
return v___x_2410_;
}
}
}
else
{
lean_object* v_val_2413_; uint8_t v___x_2414_; lean_object* v___x_2415_; lean_object* v_a_2416_; lean_object* v_a_2417_; lean_object* v___x_2419_; uint8_t v_isShared_2420_; uint8_t v_isSharedCheck_2464_; 
v_val_2413_ = lean_ctor_get(v_presentation_2361_, 0);
lean_inc(v_val_2413_);
lean_dec_ref_known(v_presentation_2361_, 1);
v___x_2414_ = lean_unbox(v_val_2413_);
lean_dec(v_val_2413_);
v___x_2415_ = l___private_Std_Time_Notation_0__Std_Time_convertText(v___x_2414_, v_a_1718_, v_a_1719_);
v_a_2416_ = lean_ctor_get(v___x_2415_, 0);
v_a_2417_ = lean_ctor_get(v___x_2415_, 1);
v_isSharedCheck_2464_ = !lean_is_exclusive(v___x_2415_);
if (v_isSharedCheck_2464_ == 0)
{
v___x_2419_ = v___x_2415_;
v_isShared_2420_ = v_isSharedCheck_2464_;
goto v_resetjp_2418_;
}
else
{
lean_inc(v_a_2417_);
lean_inc(v_a_2416_);
lean_dec(v___x_2415_);
v___x_2419_ = lean_box(0);
v_isShared_2420_ = v_isSharedCheck_2464_;
goto v_resetjp_2418_;
}
v_resetjp_2418_:
{
lean_object* v_quotContext_2421_; lean_object* v_currMacroScope_2422_; lean_object* v_ref_2423_; uint8_t v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2462_; 
v_quotContext_2421_ = lean_ctor_get(v_a_1718_, 1);
v_currMacroScope_2422_ = lean_ctor_get(v_a_1718_, 2);
v_ref_2423_ = lean_ctor_get(v_a_1718_, 5);
v___x_2424_ = 0;
v___x_2425_ = l_Lean_SourceInfo_fromRef(v_ref_2423_, v___x_2424_);
v___x_2426_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2427_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__141, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__141_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__141);
v___x_2428_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__143));
lean_inc_n(v_currMacroScope_2422_, 3);
lean_inc_n(v_quotContext_2421_, 3);
v___x_2429_ = l_Lean_addMacroScope(v_quotContext_2421_, v___x_2428_, v_currMacroScope_2422_);
v___x_2430_ = lean_box(0);
v___x_2431_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__147));
lean_inc_n(v___x_2425_, 13);
v___x_2432_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2432_, 0, v___x_2425_);
lean_ctor_set(v___x_2432_, 1, v___x_2427_);
lean_ctor_set(v___x_2432_, 2, v___x_2429_);
lean_ctor_set(v___x_2432_, 3, v___x_2431_);
v___x_2433_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2434_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__42));
v___x_2435_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__44));
v___x_2436_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__45));
v___x_2437_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2437_, 0, v___x_2425_);
lean_ctor_set(v___x_2437_, 1, v___x_2436_);
v___x_2438_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__47));
v___x_2439_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49);
v___x_2440_ = lean_box(0);
v___x_2441_ = l_Lean_addMacroScope(v_quotContext_2421_, v___x_2440_, v_currMacroScope_2422_);
v___x_2442_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__65));
v___x_2443_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2443_, 0, v___x_2425_);
lean_ctor_set(v___x_2443_, 1, v___x_2439_);
lean_ctor_set(v___x_2443_, 2, v___x_2441_);
lean_ctor_set(v___x_2443_, 3, v___x_2442_);
v___x_2444_ = l_Lean_Syntax_node1(v___x_2425_, v___x_2438_, v___x_2443_);
v___x_2445_ = l_Lean_Syntax_node2(v___x_2425_, v___x_2435_, v___x_2437_, v___x_2444_);
v___x_2446_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__67));
v___x_2447_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__68));
v___x_2448_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2448_, 0, v___x_2425_);
lean_ctor_set(v___x_2448_, 1, v___x_2447_);
v___x_2449_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__74, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__74_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__74);
v___x_2450_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__75));
v___x_2451_ = l_Lean_addMacroScope(v_quotContext_2421_, v___x_2450_, v_currMacroScope_2422_);
v___x_2452_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2452_, 0, v___x_2425_);
lean_ctor_set(v___x_2452_, 1, v___x_2449_);
lean_ctor_set(v___x_2452_, 2, v___x_2451_);
lean_ctor_set(v___x_2452_, 3, v___x_2430_);
v___x_2453_ = l_Lean_Syntax_node2(v___x_2425_, v___x_2446_, v___x_2448_, v___x_2452_);
v___x_2454_ = l_Lean_Syntax_node1(v___x_2425_, v___x_2433_, v_a_2416_);
v___x_2455_ = l_Lean_Syntax_node2(v___x_2425_, v___x_2426_, v___x_2453_, v___x_2454_);
v___x_2456_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__72));
v___x_2457_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2457_, 0, v___x_2425_);
lean_ctor_set(v___x_2457_, 1, v___x_2456_);
v___x_2458_ = l_Lean_Syntax_node3(v___x_2425_, v___x_2434_, v___x_2445_, v___x_2455_, v___x_2457_);
v___x_2459_ = l_Lean_Syntax_node1(v___x_2425_, v___x_2433_, v___x_2458_);
v___x_2460_ = l_Lean_Syntax_node2(v___x_2425_, v___x_2426_, v___x_2432_, v___x_2459_);
if (v_isShared_2420_ == 0)
{
lean_ctor_set(v___x_2419_, 0, v___x_2460_);
v___x_2462_ = v___x_2419_;
goto v_reusejp_2461_;
}
else
{
lean_object* v_reuseFailAlloc_2463_; 
v_reuseFailAlloc_2463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2463_, 0, v___x_2460_);
lean_ctor_set(v_reuseFailAlloc_2463_, 1, v_a_2417_);
v___x_2462_ = v_reuseFailAlloc_2463_;
goto v_reusejp_2461_;
}
v_reusejp_2461_:
{
return v___x_2462_;
}
}
}
}
case 14:
{
lean_object* v_presentation_2465_; 
v_presentation_2465_ = lean_ctor_get(v_x_1717_, 0);
lean_inc_ref(v_presentation_2465_);
lean_dec_ref_known(v_x_1717_, 1);
if (lean_obj_tag(v_presentation_2465_) == 0)
{
lean_object* v_val_2466_; lean_object* v___x_2467_; lean_object* v_a_2468_; lean_object* v_a_2469_; lean_object* v___x_2471_; uint8_t v_isShared_2472_; uint8_t v_isSharedCheck_2516_; 
v_val_2466_ = lean_ctor_get(v_presentation_2465_, 0);
lean_inc(v_val_2466_);
lean_dec_ref_known(v_presentation_2465_, 1);
v___x_2467_ = l___private_Std_Time_Notation_0__Std_Time_convertNumber(v_val_2466_, v_a_1718_, v_a_1719_);
v_a_2468_ = lean_ctor_get(v___x_2467_, 0);
v_a_2469_ = lean_ctor_get(v___x_2467_, 1);
v_isSharedCheck_2516_ = !lean_is_exclusive(v___x_2467_);
if (v_isSharedCheck_2516_ == 0)
{
v___x_2471_ = v___x_2467_;
v_isShared_2472_ = v_isSharedCheck_2516_;
goto v_resetjp_2470_;
}
else
{
lean_inc(v_a_2469_);
lean_inc(v_a_2468_);
lean_dec(v___x_2467_);
v___x_2471_ = lean_box(0);
v_isShared_2472_ = v_isSharedCheck_2516_;
goto v_resetjp_2470_;
}
v_resetjp_2470_:
{
lean_object* v_quotContext_2473_; lean_object* v_currMacroScope_2474_; lean_object* v_ref_2475_; uint8_t v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2514_; 
v_quotContext_2473_ = lean_ctor_get(v_a_1718_, 1);
v_currMacroScope_2474_ = lean_ctor_get(v_a_1718_, 2);
v_ref_2475_ = lean_ctor_get(v_a_1718_, 5);
v___x_2476_ = 0;
v___x_2477_ = l_Lean_SourceInfo_fromRef(v_ref_2475_, v___x_2476_);
v___x_2478_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2479_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__149, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__149_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__149);
v___x_2480_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__151));
lean_inc_n(v_currMacroScope_2474_, 3);
lean_inc_n(v_quotContext_2473_, 3);
v___x_2481_ = l_Lean_addMacroScope(v_quotContext_2473_, v___x_2480_, v_currMacroScope_2474_);
v___x_2482_ = lean_box(0);
v___x_2483_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__155));
lean_inc_n(v___x_2477_, 13);
v___x_2484_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2484_, 0, v___x_2477_);
lean_ctor_set(v___x_2484_, 1, v___x_2479_);
lean_ctor_set(v___x_2484_, 2, v___x_2481_);
lean_ctor_set(v___x_2484_, 3, v___x_2483_);
v___x_2485_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2486_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__42));
v___x_2487_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__44));
v___x_2488_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__45));
v___x_2489_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2489_, 0, v___x_2477_);
lean_ctor_set(v___x_2489_, 1, v___x_2488_);
v___x_2490_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__47));
v___x_2491_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49);
v___x_2492_ = lean_box(0);
v___x_2493_ = l_Lean_addMacroScope(v_quotContext_2473_, v___x_2492_, v_currMacroScope_2474_);
v___x_2494_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__65));
v___x_2495_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2495_, 0, v___x_2477_);
lean_ctor_set(v___x_2495_, 1, v___x_2491_);
lean_ctor_set(v___x_2495_, 2, v___x_2493_);
lean_ctor_set(v___x_2495_, 3, v___x_2494_);
v___x_2496_ = l_Lean_Syntax_node1(v___x_2477_, v___x_2490_, v___x_2495_);
v___x_2497_ = l_Lean_Syntax_node2(v___x_2477_, v___x_2487_, v___x_2489_, v___x_2496_);
v___x_2498_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__67));
v___x_2499_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__68));
v___x_2500_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2500_, 0, v___x_2477_);
lean_ctor_set(v___x_2500_, 1, v___x_2499_);
v___x_2501_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__70, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__70_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__70);
v___x_2502_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__71));
v___x_2503_ = l_Lean_addMacroScope(v_quotContext_2473_, v___x_2502_, v_currMacroScope_2474_);
v___x_2504_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2504_, 0, v___x_2477_);
lean_ctor_set(v___x_2504_, 1, v___x_2501_);
lean_ctor_set(v___x_2504_, 2, v___x_2503_);
lean_ctor_set(v___x_2504_, 3, v___x_2482_);
v___x_2505_ = l_Lean_Syntax_node2(v___x_2477_, v___x_2498_, v___x_2500_, v___x_2504_);
v___x_2506_ = l_Lean_Syntax_node1(v___x_2477_, v___x_2485_, v_a_2468_);
v___x_2507_ = l_Lean_Syntax_node2(v___x_2477_, v___x_2478_, v___x_2505_, v___x_2506_);
v___x_2508_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__72));
v___x_2509_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2509_, 0, v___x_2477_);
lean_ctor_set(v___x_2509_, 1, v___x_2508_);
v___x_2510_ = l_Lean_Syntax_node3(v___x_2477_, v___x_2486_, v___x_2497_, v___x_2507_, v___x_2509_);
v___x_2511_ = l_Lean_Syntax_node1(v___x_2477_, v___x_2485_, v___x_2510_);
v___x_2512_ = l_Lean_Syntax_node2(v___x_2477_, v___x_2478_, v___x_2484_, v___x_2511_);
if (v_isShared_2472_ == 0)
{
lean_ctor_set(v___x_2471_, 0, v___x_2512_);
v___x_2514_ = v___x_2471_;
goto v_reusejp_2513_;
}
else
{
lean_object* v_reuseFailAlloc_2515_; 
v_reuseFailAlloc_2515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2515_, 0, v___x_2512_);
lean_ctor_set(v_reuseFailAlloc_2515_, 1, v_a_2469_);
v___x_2514_ = v_reuseFailAlloc_2515_;
goto v_reusejp_2513_;
}
v_reusejp_2513_:
{
return v___x_2514_;
}
}
}
else
{
lean_object* v_val_2517_; uint8_t v___x_2518_; lean_object* v___x_2519_; lean_object* v_a_2520_; lean_object* v_a_2521_; lean_object* v___x_2523_; uint8_t v_isShared_2524_; uint8_t v_isSharedCheck_2568_; 
v_val_2517_ = lean_ctor_get(v_presentation_2465_, 0);
lean_inc(v_val_2517_);
lean_dec_ref_known(v_presentation_2465_, 1);
v___x_2518_ = lean_unbox(v_val_2517_);
lean_dec(v_val_2517_);
v___x_2519_ = l___private_Std_Time_Notation_0__Std_Time_convertText(v___x_2518_, v_a_1718_, v_a_1719_);
v_a_2520_ = lean_ctor_get(v___x_2519_, 0);
v_a_2521_ = lean_ctor_get(v___x_2519_, 1);
v_isSharedCheck_2568_ = !lean_is_exclusive(v___x_2519_);
if (v_isSharedCheck_2568_ == 0)
{
v___x_2523_ = v___x_2519_;
v_isShared_2524_ = v_isSharedCheck_2568_;
goto v_resetjp_2522_;
}
else
{
lean_inc(v_a_2521_);
lean_inc(v_a_2520_);
lean_dec(v___x_2519_);
v___x_2523_ = lean_box(0);
v_isShared_2524_ = v_isSharedCheck_2568_;
goto v_resetjp_2522_;
}
v_resetjp_2522_:
{
lean_object* v_quotContext_2525_; lean_object* v_currMacroScope_2526_; lean_object* v_ref_2527_; uint8_t v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2566_; 
v_quotContext_2525_ = lean_ctor_get(v_a_1718_, 1);
v_currMacroScope_2526_ = lean_ctor_get(v_a_1718_, 2);
v_ref_2527_ = lean_ctor_get(v_a_1718_, 5);
v___x_2528_ = 0;
v___x_2529_ = l_Lean_SourceInfo_fromRef(v_ref_2527_, v___x_2528_);
v___x_2530_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2531_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__149, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__149_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__149);
v___x_2532_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__151));
lean_inc_n(v_currMacroScope_2526_, 3);
lean_inc_n(v_quotContext_2525_, 3);
v___x_2533_ = l_Lean_addMacroScope(v_quotContext_2525_, v___x_2532_, v_currMacroScope_2526_);
v___x_2534_ = lean_box(0);
v___x_2535_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__155));
lean_inc_n(v___x_2529_, 13);
v___x_2536_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2536_, 0, v___x_2529_);
lean_ctor_set(v___x_2536_, 1, v___x_2531_);
lean_ctor_set(v___x_2536_, 2, v___x_2533_);
lean_ctor_set(v___x_2536_, 3, v___x_2535_);
v___x_2537_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2538_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__42));
v___x_2539_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__44));
v___x_2540_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__45));
v___x_2541_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2541_, 0, v___x_2529_);
lean_ctor_set(v___x_2541_, 1, v___x_2540_);
v___x_2542_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__47));
v___x_2543_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49);
v___x_2544_ = lean_box(0);
v___x_2545_ = l_Lean_addMacroScope(v_quotContext_2525_, v___x_2544_, v_currMacroScope_2526_);
v___x_2546_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__65));
v___x_2547_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2547_, 0, v___x_2529_);
lean_ctor_set(v___x_2547_, 1, v___x_2543_);
lean_ctor_set(v___x_2547_, 2, v___x_2545_);
lean_ctor_set(v___x_2547_, 3, v___x_2546_);
v___x_2548_ = l_Lean_Syntax_node1(v___x_2529_, v___x_2542_, v___x_2547_);
v___x_2549_ = l_Lean_Syntax_node2(v___x_2529_, v___x_2539_, v___x_2541_, v___x_2548_);
v___x_2550_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__67));
v___x_2551_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__68));
v___x_2552_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2552_, 0, v___x_2529_);
lean_ctor_set(v___x_2552_, 1, v___x_2551_);
v___x_2553_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__74, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__74_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__74);
v___x_2554_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__75));
v___x_2555_ = l_Lean_addMacroScope(v_quotContext_2525_, v___x_2554_, v_currMacroScope_2526_);
v___x_2556_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2556_, 0, v___x_2529_);
lean_ctor_set(v___x_2556_, 1, v___x_2553_);
lean_ctor_set(v___x_2556_, 2, v___x_2555_);
lean_ctor_set(v___x_2556_, 3, v___x_2534_);
v___x_2557_ = l_Lean_Syntax_node2(v___x_2529_, v___x_2550_, v___x_2552_, v___x_2556_);
v___x_2558_ = l_Lean_Syntax_node1(v___x_2529_, v___x_2537_, v_a_2520_);
v___x_2559_ = l_Lean_Syntax_node2(v___x_2529_, v___x_2530_, v___x_2557_, v___x_2558_);
v___x_2560_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__72));
v___x_2561_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2561_, 0, v___x_2529_);
lean_ctor_set(v___x_2561_, 1, v___x_2560_);
v___x_2562_ = l_Lean_Syntax_node3(v___x_2529_, v___x_2538_, v___x_2549_, v___x_2559_, v___x_2561_);
v___x_2563_ = l_Lean_Syntax_node1(v___x_2529_, v___x_2537_, v___x_2562_);
v___x_2564_ = l_Lean_Syntax_node2(v___x_2529_, v___x_2530_, v___x_2536_, v___x_2563_);
if (v_isShared_2524_ == 0)
{
lean_ctor_set(v___x_2523_, 0, v___x_2564_);
v___x_2566_ = v___x_2523_;
goto v_reusejp_2565_;
}
else
{
lean_object* v_reuseFailAlloc_2567_; 
v_reuseFailAlloc_2567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2567_, 0, v___x_2564_);
lean_ctor_set(v_reuseFailAlloc_2567_, 1, v_a_2521_);
v___x_2566_ = v_reuseFailAlloc_2567_;
goto v_reusejp_2565_;
}
v_reusejp_2565_:
{
return v___x_2566_;
}
}
}
}
case 15:
{
lean_object* v_presentation_2569_; lean_object* v___x_2570_; lean_object* v_a_2571_; lean_object* v_a_2572_; lean_object* v___x_2574_; uint8_t v_isShared_2575_; uint8_t v_isSharedCheck_2593_; 
v_presentation_2569_ = lean_ctor_get(v_x_1717_, 0);
lean_inc(v_presentation_2569_);
lean_dec_ref_known(v_x_1717_, 1);
v___x_2570_ = l___private_Std_Time_Notation_0__Std_Time_convertNumber(v_presentation_2569_, v_a_1718_, v_a_1719_);
v_a_2571_ = lean_ctor_get(v___x_2570_, 0);
v_a_2572_ = lean_ctor_get(v___x_2570_, 1);
v_isSharedCheck_2593_ = !lean_is_exclusive(v___x_2570_);
if (v_isSharedCheck_2593_ == 0)
{
v___x_2574_ = v___x_2570_;
v_isShared_2575_ = v_isSharedCheck_2593_;
goto v_resetjp_2573_;
}
else
{
lean_inc(v_a_2572_);
lean_inc(v_a_2571_);
lean_dec(v___x_2570_);
v___x_2574_ = lean_box(0);
v_isShared_2575_ = v_isSharedCheck_2593_;
goto v_resetjp_2573_;
}
v_resetjp_2573_:
{
lean_object* v_quotContext_2576_; lean_object* v_currMacroScope_2577_; lean_object* v_ref_2578_; uint8_t v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2591_; 
v_quotContext_2576_ = lean_ctor_get(v_a_1718_, 1);
v_currMacroScope_2577_ = lean_ctor_get(v_a_1718_, 2);
v_ref_2578_ = lean_ctor_get(v_a_1718_, 5);
v___x_2579_ = 0;
v___x_2580_ = l_Lean_SourceInfo_fromRef(v_ref_2578_, v___x_2579_);
v___x_2581_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2582_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__157, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__157_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__157);
v___x_2583_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__159));
lean_inc(v_currMacroScope_2577_);
lean_inc(v_quotContext_2576_);
v___x_2584_ = l_Lean_addMacroScope(v_quotContext_2576_, v___x_2583_, v_currMacroScope_2577_);
v___x_2585_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__163));
lean_inc_n(v___x_2580_, 2);
v___x_2586_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2586_, 0, v___x_2580_);
lean_ctor_set(v___x_2586_, 1, v___x_2582_);
lean_ctor_set(v___x_2586_, 2, v___x_2584_);
lean_ctor_set(v___x_2586_, 3, v___x_2585_);
v___x_2587_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2588_ = l_Lean_Syntax_node1(v___x_2580_, v___x_2587_, v_a_2571_);
v___x_2589_ = l_Lean_Syntax_node2(v___x_2580_, v___x_2581_, v___x_2586_, v___x_2588_);
if (v_isShared_2575_ == 0)
{
lean_ctor_set(v___x_2574_, 0, v___x_2589_);
v___x_2591_ = v___x_2574_;
goto v_reusejp_2590_;
}
else
{
lean_object* v_reuseFailAlloc_2592_; 
v_reuseFailAlloc_2592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2592_, 0, v___x_2589_);
lean_ctor_set(v_reuseFailAlloc_2592_, 1, v_a_2572_);
v___x_2591_ = v_reuseFailAlloc_2592_;
goto v_reusejp_2590_;
}
v_reusejp_2590_:
{
return v___x_2591_;
}
}
}
case 16:
{
uint8_t v_presentation_2594_; lean_object* v___x_2595_; lean_object* v_a_2596_; lean_object* v_a_2597_; lean_object* v___x_2599_; uint8_t v_isShared_2600_; uint8_t v_isSharedCheck_2618_; 
v_presentation_2594_ = lean_ctor_get_uint8(v_x_1717_, 0);
lean_dec_ref_known(v_x_1717_, 0);
v___x_2595_ = l___private_Std_Time_Notation_0__Std_Time_convertText(v_presentation_2594_, v_a_1718_, v_a_1719_);
v_a_2596_ = lean_ctor_get(v___x_2595_, 0);
v_a_2597_ = lean_ctor_get(v___x_2595_, 1);
v_isSharedCheck_2618_ = !lean_is_exclusive(v___x_2595_);
if (v_isSharedCheck_2618_ == 0)
{
v___x_2599_ = v___x_2595_;
v_isShared_2600_ = v_isSharedCheck_2618_;
goto v_resetjp_2598_;
}
else
{
lean_inc(v_a_2597_);
lean_inc(v_a_2596_);
lean_dec(v___x_2595_);
v___x_2599_ = lean_box(0);
v_isShared_2600_ = v_isSharedCheck_2618_;
goto v_resetjp_2598_;
}
v_resetjp_2598_:
{
lean_object* v_quotContext_2601_; lean_object* v_currMacroScope_2602_; lean_object* v_ref_2603_; uint8_t v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2616_; 
v_quotContext_2601_ = lean_ctor_get(v_a_1718_, 1);
v_currMacroScope_2602_ = lean_ctor_get(v_a_1718_, 2);
v_ref_2603_ = lean_ctor_get(v_a_1718_, 5);
v___x_2604_ = 0;
v___x_2605_ = l_Lean_SourceInfo_fromRef(v_ref_2603_, v___x_2604_);
v___x_2606_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2607_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__165, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__165_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__165);
v___x_2608_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__167));
lean_inc(v_currMacroScope_2602_);
lean_inc(v_quotContext_2601_);
v___x_2609_ = l_Lean_addMacroScope(v_quotContext_2601_, v___x_2608_, v_currMacroScope_2602_);
v___x_2610_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__171));
lean_inc_n(v___x_2605_, 2);
v___x_2611_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2611_, 0, v___x_2605_);
lean_ctor_set(v___x_2611_, 1, v___x_2607_);
lean_ctor_set(v___x_2611_, 2, v___x_2609_);
lean_ctor_set(v___x_2611_, 3, v___x_2610_);
v___x_2612_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2613_ = l_Lean_Syntax_node1(v___x_2605_, v___x_2612_, v_a_2596_);
v___x_2614_ = l_Lean_Syntax_node2(v___x_2605_, v___x_2606_, v___x_2611_, v___x_2613_);
if (v_isShared_2600_ == 0)
{
lean_ctor_set(v___x_2599_, 0, v___x_2614_);
v___x_2616_ = v___x_2599_;
goto v_reusejp_2615_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v___x_2614_);
lean_ctor_set(v_reuseFailAlloc_2617_, 1, v_a_2597_);
v___x_2616_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2615_;
}
v_reusejp_2615_:
{
return v___x_2616_;
}
}
}
case 17:
{
uint8_t v_presentation_2619_; lean_object* v___x_2620_; lean_object* v_a_2621_; lean_object* v_a_2622_; lean_object* v___x_2624_; uint8_t v_isShared_2625_; uint8_t v_isSharedCheck_2643_; 
v_presentation_2619_ = lean_ctor_get_uint8(v_x_1717_, 0);
lean_dec_ref_known(v_x_1717_, 0);
v___x_2620_ = l___private_Std_Time_Notation_0__Std_Time_convertText(v_presentation_2619_, v_a_1718_, v_a_1719_);
v_a_2621_ = lean_ctor_get(v___x_2620_, 0);
v_a_2622_ = lean_ctor_get(v___x_2620_, 1);
v_isSharedCheck_2643_ = !lean_is_exclusive(v___x_2620_);
if (v_isSharedCheck_2643_ == 0)
{
v___x_2624_ = v___x_2620_;
v_isShared_2625_ = v_isSharedCheck_2643_;
goto v_resetjp_2623_;
}
else
{
lean_inc(v_a_2622_);
lean_inc(v_a_2621_);
lean_dec(v___x_2620_);
v___x_2624_ = lean_box(0);
v_isShared_2625_ = v_isSharedCheck_2643_;
goto v_resetjp_2623_;
}
v_resetjp_2623_:
{
lean_object* v_quotContext_2626_; lean_object* v_currMacroScope_2627_; lean_object* v_ref_2628_; uint8_t v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2641_; 
v_quotContext_2626_ = lean_ctor_get(v_a_1718_, 1);
v_currMacroScope_2627_ = lean_ctor_get(v_a_1718_, 2);
v_ref_2628_ = lean_ctor_get(v_a_1718_, 5);
v___x_2629_ = 0;
v___x_2630_ = l_Lean_SourceInfo_fromRef(v_ref_2628_, v___x_2629_);
v___x_2631_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2632_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__173, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__173_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__173);
v___x_2633_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__175));
lean_inc(v_currMacroScope_2627_);
lean_inc(v_quotContext_2626_);
v___x_2634_ = l_Lean_addMacroScope(v_quotContext_2626_, v___x_2633_, v_currMacroScope_2627_);
v___x_2635_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__179));
lean_inc_n(v___x_2630_, 2);
v___x_2636_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2636_, 0, v___x_2630_);
lean_ctor_set(v___x_2636_, 1, v___x_2632_);
lean_ctor_set(v___x_2636_, 2, v___x_2634_);
lean_ctor_set(v___x_2636_, 3, v___x_2635_);
v___x_2637_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2638_ = l_Lean_Syntax_node1(v___x_2630_, v___x_2637_, v_a_2621_);
v___x_2639_ = l_Lean_Syntax_node2(v___x_2630_, v___x_2631_, v___x_2636_, v___x_2638_);
if (v_isShared_2625_ == 0)
{
lean_ctor_set(v___x_2624_, 0, v___x_2639_);
v___x_2641_ = v___x_2624_;
goto v_reusejp_2640_;
}
else
{
lean_object* v_reuseFailAlloc_2642_; 
v_reuseFailAlloc_2642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2642_, 0, v___x_2639_);
lean_ctor_set(v_reuseFailAlloc_2642_, 1, v_a_2622_);
v___x_2641_ = v_reuseFailAlloc_2642_;
goto v_reusejp_2640_;
}
v_reusejp_2640_:
{
return v___x_2641_;
}
}
}
case 18:
{
uint8_t v_presentation_2644_; lean_object* v___x_2645_; lean_object* v_a_2646_; lean_object* v_a_2647_; lean_object* v___x_2649_; uint8_t v_isShared_2650_; uint8_t v_isSharedCheck_2668_; 
v_presentation_2644_ = lean_ctor_get_uint8(v_x_1717_, 0);
lean_dec_ref_known(v_x_1717_, 0);
v___x_2645_ = l___private_Std_Time_Notation_0__Std_Time_convertText(v_presentation_2644_, v_a_1718_, v_a_1719_);
v_a_2646_ = lean_ctor_get(v___x_2645_, 0);
v_a_2647_ = lean_ctor_get(v___x_2645_, 1);
v_isSharedCheck_2668_ = !lean_is_exclusive(v___x_2645_);
if (v_isSharedCheck_2668_ == 0)
{
v___x_2649_ = v___x_2645_;
v_isShared_2650_ = v_isSharedCheck_2668_;
goto v_resetjp_2648_;
}
else
{
lean_inc(v_a_2647_);
lean_inc(v_a_2646_);
lean_dec(v___x_2645_);
v___x_2649_ = lean_box(0);
v_isShared_2650_ = v_isSharedCheck_2668_;
goto v_resetjp_2648_;
}
v_resetjp_2648_:
{
lean_object* v_quotContext_2651_; lean_object* v_currMacroScope_2652_; lean_object* v_ref_2653_; uint8_t v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2666_; 
v_quotContext_2651_ = lean_ctor_get(v_a_1718_, 1);
v_currMacroScope_2652_ = lean_ctor_get(v_a_1718_, 2);
v_ref_2653_ = lean_ctor_get(v_a_1718_, 5);
v___x_2654_ = 0;
v___x_2655_ = l_Lean_SourceInfo_fromRef(v_ref_2653_, v___x_2654_);
v___x_2656_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2657_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__181, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__181_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__181);
v___x_2658_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__183));
lean_inc(v_currMacroScope_2652_);
lean_inc(v_quotContext_2651_);
v___x_2659_ = l_Lean_addMacroScope(v_quotContext_2651_, v___x_2658_, v_currMacroScope_2652_);
v___x_2660_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__187));
lean_inc_n(v___x_2655_, 2);
v___x_2661_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2661_, 0, v___x_2655_);
lean_ctor_set(v___x_2661_, 1, v___x_2657_);
lean_ctor_set(v___x_2661_, 2, v___x_2659_);
lean_ctor_set(v___x_2661_, 3, v___x_2660_);
v___x_2662_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2663_ = l_Lean_Syntax_node1(v___x_2655_, v___x_2662_, v_a_2646_);
v___x_2664_ = l_Lean_Syntax_node2(v___x_2655_, v___x_2656_, v___x_2661_, v___x_2663_);
if (v_isShared_2650_ == 0)
{
lean_ctor_set(v___x_2649_, 0, v___x_2664_);
v___x_2666_ = v___x_2649_;
goto v_reusejp_2665_;
}
else
{
lean_object* v_reuseFailAlloc_2667_; 
v_reuseFailAlloc_2667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2667_, 0, v___x_2664_);
lean_ctor_set(v_reuseFailAlloc_2667_, 1, v_a_2647_);
v___x_2666_ = v_reuseFailAlloc_2667_;
goto v_reusejp_2665_;
}
v_reusejp_2665_:
{
return v___x_2666_;
}
}
}
case 19:
{
lean_object* v_presentation_2669_; lean_object* v___x_2670_; lean_object* v_a_2671_; lean_object* v_a_2672_; lean_object* v___x_2674_; uint8_t v_isShared_2675_; uint8_t v_isSharedCheck_2693_; 
v_presentation_2669_ = lean_ctor_get(v_x_1717_, 0);
lean_inc(v_presentation_2669_);
lean_dec_ref_known(v_x_1717_, 1);
v___x_2670_ = l___private_Std_Time_Notation_0__Std_Time_convertNumber(v_presentation_2669_, v_a_1718_, v_a_1719_);
v_a_2671_ = lean_ctor_get(v___x_2670_, 0);
v_a_2672_ = lean_ctor_get(v___x_2670_, 1);
v_isSharedCheck_2693_ = !lean_is_exclusive(v___x_2670_);
if (v_isSharedCheck_2693_ == 0)
{
v___x_2674_ = v___x_2670_;
v_isShared_2675_ = v_isSharedCheck_2693_;
goto v_resetjp_2673_;
}
else
{
lean_inc(v_a_2672_);
lean_inc(v_a_2671_);
lean_dec(v___x_2670_);
v___x_2674_ = lean_box(0);
v_isShared_2675_ = v_isSharedCheck_2693_;
goto v_resetjp_2673_;
}
v_resetjp_2673_:
{
lean_object* v_quotContext_2676_; lean_object* v_currMacroScope_2677_; lean_object* v_ref_2678_; uint8_t v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2691_; 
v_quotContext_2676_ = lean_ctor_get(v_a_1718_, 1);
v_currMacroScope_2677_ = lean_ctor_get(v_a_1718_, 2);
v_ref_2678_ = lean_ctor_get(v_a_1718_, 5);
v___x_2679_ = 0;
v___x_2680_ = l_Lean_SourceInfo_fromRef(v_ref_2678_, v___x_2679_);
v___x_2681_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2682_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__189, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__189_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__189);
v___x_2683_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__191));
lean_inc(v_currMacroScope_2677_);
lean_inc(v_quotContext_2676_);
v___x_2684_ = l_Lean_addMacroScope(v_quotContext_2676_, v___x_2683_, v_currMacroScope_2677_);
v___x_2685_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__195));
lean_inc_n(v___x_2680_, 2);
v___x_2686_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2686_, 0, v___x_2680_);
lean_ctor_set(v___x_2686_, 1, v___x_2682_);
lean_ctor_set(v___x_2686_, 2, v___x_2684_);
lean_ctor_set(v___x_2686_, 3, v___x_2685_);
v___x_2687_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2688_ = l_Lean_Syntax_node1(v___x_2680_, v___x_2687_, v_a_2671_);
v___x_2689_ = l_Lean_Syntax_node2(v___x_2680_, v___x_2681_, v___x_2686_, v___x_2688_);
if (v_isShared_2675_ == 0)
{
lean_ctor_set(v___x_2674_, 0, v___x_2689_);
v___x_2691_ = v___x_2674_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v___x_2689_);
lean_ctor_set(v_reuseFailAlloc_2692_, 1, v_a_2672_);
v___x_2691_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
return v___x_2691_;
}
}
}
case 20:
{
lean_object* v_presentation_2694_; lean_object* v___x_2695_; lean_object* v_a_2696_; lean_object* v_a_2697_; lean_object* v___x_2699_; uint8_t v_isShared_2700_; uint8_t v_isSharedCheck_2718_; 
v_presentation_2694_ = lean_ctor_get(v_x_1717_, 0);
lean_inc(v_presentation_2694_);
lean_dec_ref_known(v_x_1717_, 1);
v___x_2695_ = l___private_Std_Time_Notation_0__Std_Time_convertNumber(v_presentation_2694_, v_a_1718_, v_a_1719_);
v_a_2696_ = lean_ctor_get(v___x_2695_, 0);
v_a_2697_ = lean_ctor_get(v___x_2695_, 1);
v_isSharedCheck_2718_ = !lean_is_exclusive(v___x_2695_);
if (v_isSharedCheck_2718_ == 0)
{
v___x_2699_ = v___x_2695_;
v_isShared_2700_ = v_isSharedCheck_2718_;
goto v_resetjp_2698_;
}
else
{
lean_inc(v_a_2697_);
lean_inc(v_a_2696_);
lean_dec(v___x_2695_);
v___x_2699_ = lean_box(0);
v_isShared_2700_ = v_isSharedCheck_2718_;
goto v_resetjp_2698_;
}
v_resetjp_2698_:
{
lean_object* v_quotContext_2701_; lean_object* v_currMacroScope_2702_; lean_object* v_ref_2703_; uint8_t v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2716_; 
v_quotContext_2701_ = lean_ctor_get(v_a_1718_, 1);
v_currMacroScope_2702_ = lean_ctor_get(v_a_1718_, 2);
v_ref_2703_ = lean_ctor_get(v_a_1718_, 5);
v___x_2704_ = 0;
v___x_2705_ = l_Lean_SourceInfo_fromRef(v_ref_2703_, v___x_2704_);
v___x_2706_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2707_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__197, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__197_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__197);
v___x_2708_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__199));
lean_inc(v_currMacroScope_2702_);
lean_inc(v_quotContext_2701_);
v___x_2709_ = l_Lean_addMacroScope(v_quotContext_2701_, v___x_2708_, v_currMacroScope_2702_);
v___x_2710_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__203));
lean_inc_n(v___x_2705_, 2);
v___x_2711_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2711_, 0, v___x_2705_);
lean_ctor_set(v___x_2711_, 1, v___x_2707_);
lean_ctor_set(v___x_2711_, 2, v___x_2709_);
lean_ctor_set(v___x_2711_, 3, v___x_2710_);
v___x_2712_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2713_ = l_Lean_Syntax_node1(v___x_2705_, v___x_2712_, v_a_2696_);
v___x_2714_ = l_Lean_Syntax_node2(v___x_2705_, v___x_2706_, v___x_2711_, v___x_2713_);
if (v_isShared_2700_ == 0)
{
lean_ctor_set(v___x_2699_, 0, v___x_2714_);
v___x_2716_ = v___x_2699_;
goto v_reusejp_2715_;
}
else
{
lean_object* v_reuseFailAlloc_2717_; 
v_reuseFailAlloc_2717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2717_, 0, v___x_2714_);
lean_ctor_set(v_reuseFailAlloc_2717_, 1, v_a_2697_);
v___x_2716_ = v_reuseFailAlloc_2717_;
goto v_reusejp_2715_;
}
v_reusejp_2715_:
{
return v___x_2716_;
}
}
}
case 21:
{
lean_object* v_presentation_2719_; lean_object* v___x_2720_; lean_object* v_a_2721_; lean_object* v_a_2722_; lean_object* v___x_2724_; uint8_t v_isShared_2725_; uint8_t v_isSharedCheck_2743_; 
v_presentation_2719_ = lean_ctor_get(v_x_1717_, 0);
lean_inc(v_presentation_2719_);
lean_dec_ref_known(v_x_1717_, 1);
v___x_2720_ = l___private_Std_Time_Notation_0__Std_Time_convertNumber(v_presentation_2719_, v_a_1718_, v_a_1719_);
v_a_2721_ = lean_ctor_get(v___x_2720_, 0);
v_a_2722_ = lean_ctor_get(v___x_2720_, 1);
v_isSharedCheck_2743_ = !lean_is_exclusive(v___x_2720_);
if (v_isSharedCheck_2743_ == 0)
{
v___x_2724_ = v___x_2720_;
v_isShared_2725_ = v_isSharedCheck_2743_;
goto v_resetjp_2723_;
}
else
{
lean_inc(v_a_2722_);
lean_inc(v_a_2721_);
lean_dec(v___x_2720_);
v___x_2724_ = lean_box(0);
v_isShared_2725_ = v_isSharedCheck_2743_;
goto v_resetjp_2723_;
}
v_resetjp_2723_:
{
lean_object* v_quotContext_2726_; lean_object* v_currMacroScope_2727_; lean_object* v_ref_2728_; uint8_t v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2741_; 
v_quotContext_2726_ = lean_ctor_get(v_a_1718_, 1);
v_currMacroScope_2727_ = lean_ctor_get(v_a_1718_, 2);
v_ref_2728_ = lean_ctor_get(v_a_1718_, 5);
v___x_2729_ = 0;
v___x_2730_ = l_Lean_SourceInfo_fromRef(v_ref_2728_, v___x_2729_);
v___x_2731_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2732_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__205, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__205_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__205);
v___x_2733_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__207));
lean_inc(v_currMacroScope_2727_);
lean_inc(v_quotContext_2726_);
v___x_2734_ = l_Lean_addMacroScope(v_quotContext_2726_, v___x_2733_, v_currMacroScope_2727_);
v___x_2735_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__211));
lean_inc_n(v___x_2730_, 2);
v___x_2736_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2736_, 0, v___x_2730_);
lean_ctor_set(v___x_2736_, 1, v___x_2732_);
lean_ctor_set(v___x_2736_, 2, v___x_2734_);
lean_ctor_set(v___x_2736_, 3, v___x_2735_);
v___x_2737_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2738_ = l_Lean_Syntax_node1(v___x_2730_, v___x_2737_, v_a_2721_);
v___x_2739_ = l_Lean_Syntax_node2(v___x_2730_, v___x_2731_, v___x_2736_, v___x_2738_);
if (v_isShared_2725_ == 0)
{
lean_ctor_set(v___x_2724_, 0, v___x_2739_);
v___x_2741_ = v___x_2724_;
goto v_reusejp_2740_;
}
else
{
lean_object* v_reuseFailAlloc_2742_; 
v_reuseFailAlloc_2742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2742_, 0, v___x_2739_);
lean_ctor_set(v_reuseFailAlloc_2742_, 1, v_a_2722_);
v___x_2741_ = v_reuseFailAlloc_2742_;
goto v_reusejp_2740_;
}
v_reusejp_2740_:
{
return v___x_2741_;
}
}
}
case 22:
{
lean_object* v_presentation_2744_; lean_object* v___x_2745_; lean_object* v_a_2746_; lean_object* v_a_2747_; lean_object* v___x_2749_; uint8_t v_isShared_2750_; uint8_t v_isSharedCheck_2768_; 
v_presentation_2744_ = lean_ctor_get(v_x_1717_, 0);
lean_inc(v_presentation_2744_);
lean_dec_ref_known(v_x_1717_, 1);
v___x_2745_ = l___private_Std_Time_Notation_0__Std_Time_convertNumber(v_presentation_2744_, v_a_1718_, v_a_1719_);
v_a_2746_ = lean_ctor_get(v___x_2745_, 0);
v_a_2747_ = lean_ctor_get(v___x_2745_, 1);
v_isSharedCheck_2768_ = !lean_is_exclusive(v___x_2745_);
if (v_isSharedCheck_2768_ == 0)
{
v___x_2749_ = v___x_2745_;
v_isShared_2750_ = v_isSharedCheck_2768_;
goto v_resetjp_2748_;
}
else
{
lean_inc(v_a_2747_);
lean_inc(v_a_2746_);
lean_dec(v___x_2745_);
v___x_2749_ = lean_box(0);
v_isShared_2750_ = v_isSharedCheck_2768_;
goto v_resetjp_2748_;
}
v_resetjp_2748_:
{
lean_object* v_quotContext_2751_; lean_object* v_currMacroScope_2752_; lean_object* v_ref_2753_; uint8_t v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2766_; 
v_quotContext_2751_ = lean_ctor_get(v_a_1718_, 1);
v_currMacroScope_2752_ = lean_ctor_get(v_a_1718_, 2);
v_ref_2753_ = lean_ctor_get(v_a_1718_, 5);
v___x_2754_ = 0;
v___x_2755_ = l_Lean_SourceInfo_fromRef(v_ref_2753_, v___x_2754_);
v___x_2756_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2757_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__213, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__213_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__213);
v___x_2758_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__215));
lean_inc(v_currMacroScope_2752_);
lean_inc(v_quotContext_2751_);
v___x_2759_ = l_Lean_addMacroScope(v_quotContext_2751_, v___x_2758_, v_currMacroScope_2752_);
v___x_2760_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__219));
lean_inc_n(v___x_2755_, 2);
v___x_2761_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2761_, 0, v___x_2755_);
lean_ctor_set(v___x_2761_, 1, v___x_2757_);
lean_ctor_set(v___x_2761_, 2, v___x_2759_);
lean_ctor_set(v___x_2761_, 3, v___x_2760_);
v___x_2762_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2763_ = l_Lean_Syntax_node1(v___x_2755_, v___x_2762_, v_a_2746_);
v___x_2764_ = l_Lean_Syntax_node2(v___x_2755_, v___x_2756_, v___x_2761_, v___x_2763_);
if (v_isShared_2750_ == 0)
{
lean_ctor_set(v___x_2749_, 0, v___x_2764_);
v___x_2766_ = v___x_2749_;
goto v_reusejp_2765_;
}
else
{
lean_object* v_reuseFailAlloc_2767_; 
v_reuseFailAlloc_2767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2767_, 0, v___x_2764_);
lean_ctor_set(v_reuseFailAlloc_2767_, 1, v_a_2747_);
v___x_2766_ = v_reuseFailAlloc_2767_;
goto v_reusejp_2765_;
}
v_reusejp_2765_:
{
return v___x_2766_;
}
}
}
case 23:
{
lean_object* v_presentation_2769_; lean_object* v___x_2770_; lean_object* v_a_2771_; lean_object* v_a_2772_; lean_object* v___x_2774_; uint8_t v_isShared_2775_; uint8_t v_isSharedCheck_2793_; 
v_presentation_2769_ = lean_ctor_get(v_x_1717_, 0);
lean_inc(v_presentation_2769_);
lean_dec_ref_known(v_x_1717_, 1);
v___x_2770_ = l___private_Std_Time_Notation_0__Std_Time_convertNumber(v_presentation_2769_, v_a_1718_, v_a_1719_);
v_a_2771_ = lean_ctor_get(v___x_2770_, 0);
v_a_2772_ = lean_ctor_get(v___x_2770_, 1);
v_isSharedCheck_2793_ = !lean_is_exclusive(v___x_2770_);
if (v_isSharedCheck_2793_ == 0)
{
v___x_2774_ = v___x_2770_;
v_isShared_2775_ = v_isSharedCheck_2793_;
goto v_resetjp_2773_;
}
else
{
lean_inc(v_a_2772_);
lean_inc(v_a_2771_);
lean_dec(v___x_2770_);
v___x_2774_ = lean_box(0);
v_isShared_2775_ = v_isSharedCheck_2793_;
goto v_resetjp_2773_;
}
v_resetjp_2773_:
{
lean_object* v_quotContext_2776_; lean_object* v_currMacroScope_2777_; lean_object* v_ref_2778_; uint8_t v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2791_; 
v_quotContext_2776_ = lean_ctor_get(v_a_1718_, 1);
v_currMacroScope_2777_ = lean_ctor_get(v_a_1718_, 2);
v_ref_2778_ = lean_ctor_get(v_a_1718_, 5);
v___x_2779_ = 0;
v___x_2780_ = l_Lean_SourceInfo_fromRef(v_ref_2778_, v___x_2779_);
v___x_2781_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2782_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__221, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__221_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__221);
v___x_2783_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__223));
lean_inc(v_currMacroScope_2777_);
lean_inc(v_quotContext_2776_);
v___x_2784_ = l_Lean_addMacroScope(v_quotContext_2776_, v___x_2783_, v_currMacroScope_2777_);
v___x_2785_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__227));
lean_inc_n(v___x_2780_, 2);
v___x_2786_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2786_, 0, v___x_2780_);
lean_ctor_set(v___x_2786_, 1, v___x_2782_);
lean_ctor_set(v___x_2786_, 2, v___x_2784_);
lean_ctor_set(v___x_2786_, 3, v___x_2785_);
v___x_2787_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2788_ = l_Lean_Syntax_node1(v___x_2780_, v___x_2787_, v_a_2771_);
v___x_2789_ = l_Lean_Syntax_node2(v___x_2780_, v___x_2781_, v___x_2786_, v___x_2788_);
if (v_isShared_2775_ == 0)
{
lean_ctor_set(v___x_2774_, 0, v___x_2789_);
v___x_2791_ = v___x_2774_;
goto v_reusejp_2790_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v___x_2789_);
lean_ctor_set(v_reuseFailAlloc_2792_, 1, v_a_2772_);
v___x_2791_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2790_;
}
v_reusejp_2790_:
{
return v___x_2791_;
}
}
}
case 24:
{
lean_object* v_presentation_2794_; lean_object* v___x_2795_; lean_object* v_a_2796_; lean_object* v_a_2797_; lean_object* v___x_2799_; uint8_t v_isShared_2800_; uint8_t v_isSharedCheck_2818_; 
v_presentation_2794_ = lean_ctor_get(v_x_1717_, 0);
lean_inc(v_presentation_2794_);
lean_dec_ref_known(v_x_1717_, 1);
v___x_2795_ = l___private_Std_Time_Notation_0__Std_Time_convertNumber(v_presentation_2794_, v_a_1718_, v_a_1719_);
v_a_2796_ = lean_ctor_get(v___x_2795_, 0);
v_a_2797_ = lean_ctor_get(v___x_2795_, 1);
v_isSharedCheck_2818_ = !lean_is_exclusive(v___x_2795_);
if (v_isSharedCheck_2818_ == 0)
{
v___x_2799_ = v___x_2795_;
v_isShared_2800_ = v_isSharedCheck_2818_;
goto v_resetjp_2798_;
}
else
{
lean_inc(v_a_2797_);
lean_inc(v_a_2796_);
lean_dec(v___x_2795_);
v___x_2799_ = lean_box(0);
v_isShared_2800_ = v_isSharedCheck_2818_;
goto v_resetjp_2798_;
}
v_resetjp_2798_:
{
lean_object* v_quotContext_2801_; lean_object* v_currMacroScope_2802_; lean_object* v_ref_2803_; uint8_t v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2816_; 
v_quotContext_2801_ = lean_ctor_get(v_a_1718_, 1);
v_currMacroScope_2802_ = lean_ctor_get(v_a_1718_, 2);
v_ref_2803_ = lean_ctor_get(v_a_1718_, 5);
v___x_2804_ = 0;
v___x_2805_ = l_Lean_SourceInfo_fromRef(v_ref_2803_, v___x_2804_);
v___x_2806_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2807_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__229, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__229_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__229);
v___x_2808_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__231));
lean_inc(v_currMacroScope_2802_);
lean_inc(v_quotContext_2801_);
v___x_2809_ = l_Lean_addMacroScope(v_quotContext_2801_, v___x_2808_, v_currMacroScope_2802_);
v___x_2810_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__235));
lean_inc_n(v___x_2805_, 2);
v___x_2811_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2811_, 0, v___x_2805_);
lean_ctor_set(v___x_2811_, 1, v___x_2807_);
lean_ctor_set(v___x_2811_, 2, v___x_2809_);
lean_ctor_set(v___x_2811_, 3, v___x_2810_);
v___x_2812_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2813_ = l_Lean_Syntax_node1(v___x_2805_, v___x_2812_, v_a_2796_);
v___x_2814_ = l_Lean_Syntax_node2(v___x_2805_, v___x_2806_, v___x_2811_, v___x_2813_);
if (v_isShared_2800_ == 0)
{
lean_ctor_set(v___x_2799_, 0, v___x_2814_);
v___x_2816_ = v___x_2799_;
goto v_reusejp_2815_;
}
else
{
lean_object* v_reuseFailAlloc_2817_; 
v_reuseFailAlloc_2817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2817_, 0, v___x_2814_);
lean_ctor_set(v_reuseFailAlloc_2817_, 1, v_a_2797_);
v___x_2816_ = v_reuseFailAlloc_2817_;
goto v_reusejp_2815_;
}
v_reusejp_2815_:
{
return v___x_2816_;
}
}
}
case 25:
{
lean_object* v_presentation_2819_; lean_object* v___x_2820_; lean_object* v_a_2821_; lean_object* v_a_2822_; lean_object* v___x_2824_; uint8_t v_isShared_2825_; uint8_t v_isSharedCheck_2843_; 
v_presentation_2819_ = lean_ctor_get(v_x_1717_, 0);
lean_inc(v_presentation_2819_);
lean_dec_ref_known(v_x_1717_, 1);
v___x_2820_ = l___private_Std_Time_Notation_0__Std_Time_convertFraction(v_presentation_2819_, v_a_1718_, v_a_1719_);
v_a_2821_ = lean_ctor_get(v___x_2820_, 0);
v_a_2822_ = lean_ctor_get(v___x_2820_, 1);
v_isSharedCheck_2843_ = !lean_is_exclusive(v___x_2820_);
if (v_isSharedCheck_2843_ == 0)
{
v___x_2824_ = v___x_2820_;
v_isShared_2825_ = v_isSharedCheck_2843_;
goto v_resetjp_2823_;
}
else
{
lean_inc(v_a_2822_);
lean_inc(v_a_2821_);
lean_dec(v___x_2820_);
v___x_2824_ = lean_box(0);
v_isShared_2825_ = v_isSharedCheck_2843_;
goto v_resetjp_2823_;
}
v_resetjp_2823_:
{
lean_object* v_quotContext_2826_; lean_object* v_currMacroScope_2827_; lean_object* v_ref_2828_; uint8_t v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2841_; 
v_quotContext_2826_ = lean_ctor_get(v_a_1718_, 1);
v_currMacroScope_2827_ = lean_ctor_get(v_a_1718_, 2);
v_ref_2828_ = lean_ctor_get(v_a_1718_, 5);
v___x_2829_ = 0;
v___x_2830_ = l_Lean_SourceInfo_fromRef(v_ref_2828_, v___x_2829_);
v___x_2831_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2832_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__237, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__237_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__237);
v___x_2833_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__239));
lean_inc(v_currMacroScope_2827_);
lean_inc(v_quotContext_2826_);
v___x_2834_ = l_Lean_addMacroScope(v_quotContext_2826_, v___x_2833_, v_currMacroScope_2827_);
v___x_2835_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__243));
lean_inc_n(v___x_2830_, 2);
v___x_2836_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2836_, 0, v___x_2830_);
lean_ctor_set(v___x_2836_, 1, v___x_2832_);
lean_ctor_set(v___x_2836_, 2, v___x_2834_);
lean_ctor_set(v___x_2836_, 3, v___x_2835_);
v___x_2837_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2838_ = l_Lean_Syntax_node1(v___x_2830_, v___x_2837_, v_a_2821_);
v___x_2839_ = l_Lean_Syntax_node2(v___x_2830_, v___x_2831_, v___x_2836_, v___x_2838_);
if (v_isShared_2825_ == 0)
{
lean_ctor_set(v___x_2824_, 0, v___x_2839_);
v___x_2841_ = v___x_2824_;
goto v_reusejp_2840_;
}
else
{
lean_object* v_reuseFailAlloc_2842_; 
v_reuseFailAlloc_2842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2842_, 0, v___x_2839_);
lean_ctor_set(v_reuseFailAlloc_2842_, 1, v_a_2822_);
v___x_2841_ = v_reuseFailAlloc_2842_;
goto v_reusejp_2840_;
}
v_reusejp_2840_:
{
return v___x_2841_;
}
}
}
case 26:
{
lean_object* v_presentation_2844_; lean_object* v___x_2845_; lean_object* v_a_2846_; lean_object* v_a_2847_; lean_object* v___x_2849_; uint8_t v_isShared_2850_; uint8_t v_isSharedCheck_2868_; 
v_presentation_2844_ = lean_ctor_get(v_x_1717_, 0);
lean_inc(v_presentation_2844_);
lean_dec_ref_known(v_x_1717_, 1);
v___x_2845_ = l___private_Std_Time_Notation_0__Std_Time_convertNumber(v_presentation_2844_, v_a_1718_, v_a_1719_);
v_a_2846_ = lean_ctor_get(v___x_2845_, 0);
v_a_2847_ = lean_ctor_get(v___x_2845_, 1);
v_isSharedCheck_2868_ = !lean_is_exclusive(v___x_2845_);
if (v_isSharedCheck_2868_ == 0)
{
v___x_2849_ = v___x_2845_;
v_isShared_2850_ = v_isSharedCheck_2868_;
goto v_resetjp_2848_;
}
else
{
lean_inc(v_a_2847_);
lean_inc(v_a_2846_);
lean_dec(v___x_2845_);
v___x_2849_ = lean_box(0);
v_isShared_2850_ = v_isSharedCheck_2868_;
goto v_resetjp_2848_;
}
v_resetjp_2848_:
{
lean_object* v_quotContext_2851_; lean_object* v_currMacroScope_2852_; lean_object* v_ref_2853_; uint8_t v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2866_; 
v_quotContext_2851_ = lean_ctor_get(v_a_1718_, 1);
v_currMacroScope_2852_ = lean_ctor_get(v_a_1718_, 2);
v_ref_2853_ = lean_ctor_get(v_a_1718_, 5);
v___x_2854_ = 0;
v___x_2855_ = l_Lean_SourceInfo_fromRef(v_ref_2853_, v___x_2854_);
v___x_2856_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2857_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__245, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__245_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__245);
v___x_2858_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__247));
lean_inc(v_currMacroScope_2852_);
lean_inc(v_quotContext_2851_);
v___x_2859_ = l_Lean_addMacroScope(v_quotContext_2851_, v___x_2858_, v_currMacroScope_2852_);
v___x_2860_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__251));
lean_inc_n(v___x_2855_, 2);
v___x_2861_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2861_, 0, v___x_2855_);
lean_ctor_set(v___x_2861_, 1, v___x_2857_);
lean_ctor_set(v___x_2861_, 2, v___x_2859_);
lean_ctor_set(v___x_2861_, 3, v___x_2860_);
v___x_2862_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2863_ = l_Lean_Syntax_node1(v___x_2855_, v___x_2862_, v_a_2846_);
v___x_2864_ = l_Lean_Syntax_node2(v___x_2855_, v___x_2856_, v___x_2861_, v___x_2863_);
if (v_isShared_2850_ == 0)
{
lean_ctor_set(v___x_2849_, 0, v___x_2864_);
v___x_2866_ = v___x_2849_;
goto v_reusejp_2865_;
}
else
{
lean_object* v_reuseFailAlloc_2867_; 
v_reuseFailAlloc_2867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2867_, 0, v___x_2864_);
lean_ctor_set(v_reuseFailAlloc_2867_, 1, v_a_2847_);
v___x_2866_ = v_reuseFailAlloc_2867_;
goto v_reusejp_2865_;
}
v_reusejp_2865_:
{
return v___x_2866_;
}
}
}
case 27:
{
lean_object* v_presentation_2869_; lean_object* v___x_2870_; lean_object* v_a_2871_; lean_object* v_a_2872_; lean_object* v___x_2874_; uint8_t v_isShared_2875_; uint8_t v_isSharedCheck_2893_; 
v_presentation_2869_ = lean_ctor_get(v_x_1717_, 0);
lean_inc(v_presentation_2869_);
lean_dec_ref_known(v_x_1717_, 1);
v___x_2870_ = l___private_Std_Time_Notation_0__Std_Time_convertNumber(v_presentation_2869_, v_a_1718_, v_a_1719_);
v_a_2871_ = lean_ctor_get(v___x_2870_, 0);
v_a_2872_ = lean_ctor_get(v___x_2870_, 1);
v_isSharedCheck_2893_ = !lean_is_exclusive(v___x_2870_);
if (v_isSharedCheck_2893_ == 0)
{
v___x_2874_ = v___x_2870_;
v_isShared_2875_ = v_isSharedCheck_2893_;
goto v_resetjp_2873_;
}
else
{
lean_inc(v_a_2872_);
lean_inc(v_a_2871_);
lean_dec(v___x_2870_);
v___x_2874_ = lean_box(0);
v_isShared_2875_ = v_isSharedCheck_2893_;
goto v_resetjp_2873_;
}
v_resetjp_2873_:
{
lean_object* v_quotContext_2876_; lean_object* v_currMacroScope_2877_; lean_object* v_ref_2878_; uint8_t v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2891_; 
v_quotContext_2876_ = lean_ctor_get(v_a_1718_, 1);
v_currMacroScope_2877_ = lean_ctor_get(v_a_1718_, 2);
v_ref_2878_ = lean_ctor_get(v_a_1718_, 5);
v___x_2879_ = 0;
v___x_2880_ = l_Lean_SourceInfo_fromRef(v_ref_2878_, v___x_2879_);
v___x_2881_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2882_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__253, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__253_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__253);
v___x_2883_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__255));
lean_inc(v_currMacroScope_2877_);
lean_inc(v_quotContext_2876_);
v___x_2884_ = l_Lean_addMacroScope(v_quotContext_2876_, v___x_2883_, v_currMacroScope_2877_);
v___x_2885_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__259));
lean_inc_n(v___x_2880_, 2);
v___x_2886_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2886_, 0, v___x_2880_);
lean_ctor_set(v___x_2886_, 1, v___x_2882_);
lean_ctor_set(v___x_2886_, 2, v___x_2884_);
lean_ctor_set(v___x_2886_, 3, v___x_2885_);
v___x_2887_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2888_ = l_Lean_Syntax_node1(v___x_2880_, v___x_2887_, v_a_2871_);
v___x_2889_ = l_Lean_Syntax_node2(v___x_2880_, v___x_2881_, v___x_2886_, v___x_2888_);
if (v_isShared_2875_ == 0)
{
lean_ctor_set(v___x_2874_, 0, v___x_2889_);
v___x_2891_ = v___x_2874_;
goto v_reusejp_2890_;
}
else
{
lean_object* v_reuseFailAlloc_2892_; 
v_reuseFailAlloc_2892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2892_, 0, v___x_2889_);
lean_ctor_set(v_reuseFailAlloc_2892_, 1, v_a_2872_);
v___x_2891_ = v_reuseFailAlloc_2892_;
goto v_reusejp_2890_;
}
v_reusejp_2890_:
{
return v___x_2891_;
}
}
}
case 28:
{
lean_object* v_presentation_2894_; lean_object* v___x_2895_; lean_object* v_a_2896_; lean_object* v_a_2897_; lean_object* v___x_2899_; uint8_t v_isShared_2900_; uint8_t v_isSharedCheck_2918_; 
v_presentation_2894_ = lean_ctor_get(v_x_1717_, 0);
lean_inc(v_presentation_2894_);
lean_dec_ref_known(v_x_1717_, 1);
v___x_2895_ = l___private_Std_Time_Notation_0__Std_Time_convertNumber(v_presentation_2894_, v_a_1718_, v_a_1719_);
v_a_2896_ = lean_ctor_get(v___x_2895_, 0);
v_a_2897_ = lean_ctor_get(v___x_2895_, 1);
v_isSharedCheck_2918_ = !lean_is_exclusive(v___x_2895_);
if (v_isSharedCheck_2918_ == 0)
{
v___x_2899_ = v___x_2895_;
v_isShared_2900_ = v_isSharedCheck_2918_;
goto v_resetjp_2898_;
}
else
{
lean_inc(v_a_2897_);
lean_inc(v_a_2896_);
lean_dec(v___x_2895_);
v___x_2899_ = lean_box(0);
v_isShared_2900_ = v_isSharedCheck_2918_;
goto v_resetjp_2898_;
}
v_resetjp_2898_:
{
lean_object* v_quotContext_2901_; lean_object* v_currMacroScope_2902_; lean_object* v_ref_2903_; uint8_t v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2916_; 
v_quotContext_2901_ = lean_ctor_get(v_a_1718_, 1);
v_currMacroScope_2902_ = lean_ctor_get(v_a_1718_, 2);
v_ref_2903_ = lean_ctor_get(v_a_1718_, 5);
v___x_2904_ = 0;
v___x_2905_ = l_Lean_SourceInfo_fromRef(v_ref_2903_, v___x_2904_);
v___x_2906_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2907_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__261, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__261_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__261);
v___x_2908_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__263));
lean_inc(v_currMacroScope_2902_);
lean_inc(v_quotContext_2901_);
v___x_2909_ = l_Lean_addMacroScope(v_quotContext_2901_, v___x_2908_, v_currMacroScope_2902_);
v___x_2910_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__267));
lean_inc_n(v___x_2905_, 2);
v___x_2911_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2911_, 0, v___x_2905_);
lean_ctor_set(v___x_2911_, 1, v___x_2907_);
lean_ctor_set(v___x_2911_, 2, v___x_2909_);
lean_ctor_set(v___x_2911_, 3, v___x_2910_);
v___x_2912_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2913_ = l_Lean_Syntax_node1(v___x_2905_, v___x_2912_, v_a_2896_);
v___x_2914_ = l_Lean_Syntax_node2(v___x_2905_, v___x_2906_, v___x_2911_, v___x_2913_);
if (v_isShared_2900_ == 0)
{
lean_ctor_set(v___x_2899_, 0, v___x_2914_);
v___x_2916_ = v___x_2899_;
goto v_reusejp_2915_;
}
else
{
lean_object* v_reuseFailAlloc_2917_; 
v_reuseFailAlloc_2917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2917_, 0, v___x_2914_);
lean_ctor_set(v_reuseFailAlloc_2917_, 1, v_a_2897_);
v___x_2916_ = v_reuseFailAlloc_2917_;
goto v_reusejp_2915_;
}
v_reusejp_2915_:
{
return v___x_2916_;
}
}
}
case 29:
{
uint8_t v_presentation_2919_; lean_object* v___x_2920_; lean_object* v_a_2921_; lean_object* v_a_2922_; lean_object* v___x_2924_; uint8_t v_isShared_2925_; uint8_t v_isSharedCheck_2943_; 
v_presentation_2919_ = lean_ctor_get_uint8(v_x_1717_, 0);
lean_dec_ref_known(v_x_1717_, 0);
v___x_2920_ = l___private_Std_Time_Notation_0__Std_Time_convertZoneId(v_presentation_2919_, v_a_1718_, v_a_1719_);
v_a_2921_ = lean_ctor_get(v___x_2920_, 0);
v_a_2922_ = lean_ctor_get(v___x_2920_, 1);
v_isSharedCheck_2943_ = !lean_is_exclusive(v___x_2920_);
if (v_isSharedCheck_2943_ == 0)
{
v___x_2924_ = v___x_2920_;
v_isShared_2925_ = v_isSharedCheck_2943_;
goto v_resetjp_2923_;
}
else
{
lean_inc(v_a_2922_);
lean_inc(v_a_2921_);
lean_dec(v___x_2920_);
v___x_2924_ = lean_box(0);
v_isShared_2925_ = v_isSharedCheck_2943_;
goto v_resetjp_2923_;
}
v_resetjp_2923_:
{
lean_object* v_quotContext_2926_; lean_object* v_currMacroScope_2927_; lean_object* v_ref_2928_; uint8_t v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2941_; 
v_quotContext_2926_ = lean_ctor_get(v_a_1718_, 1);
v_currMacroScope_2927_ = lean_ctor_get(v_a_1718_, 2);
v_ref_2928_ = lean_ctor_get(v_a_1718_, 5);
v___x_2929_ = 0;
v___x_2930_ = l_Lean_SourceInfo_fromRef(v_ref_2928_, v___x_2929_);
v___x_2931_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2932_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__269, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__269_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__269);
v___x_2933_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__271));
lean_inc(v_currMacroScope_2927_);
lean_inc(v_quotContext_2926_);
v___x_2934_ = l_Lean_addMacroScope(v_quotContext_2926_, v___x_2933_, v_currMacroScope_2927_);
v___x_2935_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__275));
lean_inc_n(v___x_2930_, 2);
v___x_2936_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2936_, 0, v___x_2930_);
lean_ctor_set(v___x_2936_, 1, v___x_2932_);
lean_ctor_set(v___x_2936_, 2, v___x_2934_);
lean_ctor_set(v___x_2936_, 3, v___x_2935_);
v___x_2937_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2938_ = l_Lean_Syntax_node1(v___x_2930_, v___x_2937_, v_a_2921_);
v___x_2939_ = l_Lean_Syntax_node2(v___x_2930_, v___x_2931_, v___x_2936_, v___x_2938_);
if (v_isShared_2925_ == 0)
{
lean_ctor_set(v___x_2924_, 0, v___x_2939_);
v___x_2941_ = v___x_2924_;
goto v_reusejp_2940_;
}
else
{
lean_object* v_reuseFailAlloc_2942_; 
v_reuseFailAlloc_2942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2942_, 0, v___x_2939_);
lean_ctor_set(v_reuseFailAlloc_2942_, 1, v_a_2922_);
v___x_2941_ = v_reuseFailAlloc_2942_;
goto v_reusejp_2940_;
}
v_reusejp_2940_:
{
return v___x_2941_;
}
}
}
case 30:
{
uint8_t v_presentation_2944_; lean_object* v___x_2945_; lean_object* v_a_2946_; lean_object* v_a_2947_; lean_object* v___x_2949_; uint8_t v_isShared_2950_; uint8_t v_isSharedCheck_2968_; 
v_presentation_2944_ = lean_ctor_get_uint8(v_x_1717_, 0);
lean_dec_ref_known(v_x_1717_, 0);
v___x_2945_ = l___private_Std_Time_Notation_0__Std_Time_convertZoneName(v_presentation_2944_, v_a_1718_, v_a_1719_);
v_a_2946_ = lean_ctor_get(v___x_2945_, 0);
v_a_2947_ = lean_ctor_get(v___x_2945_, 1);
v_isSharedCheck_2968_ = !lean_is_exclusive(v___x_2945_);
if (v_isSharedCheck_2968_ == 0)
{
v___x_2949_ = v___x_2945_;
v_isShared_2950_ = v_isSharedCheck_2968_;
goto v_resetjp_2948_;
}
else
{
lean_inc(v_a_2947_);
lean_inc(v_a_2946_);
lean_dec(v___x_2945_);
v___x_2949_ = lean_box(0);
v_isShared_2950_ = v_isSharedCheck_2968_;
goto v_resetjp_2948_;
}
v_resetjp_2948_:
{
lean_object* v_quotContext_2951_; lean_object* v_currMacroScope_2952_; lean_object* v_ref_2953_; uint8_t v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2966_; 
v_quotContext_2951_ = lean_ctor_get(v_a_1718_, 1);
v_currMacroScope_2952_ = lean_ctor_get(v_a_1718_, 2);
v_ref_2953_ = lean_ctor_get(v_a_1718_, 5);
v___x_2954_ = 0;
v___x_2955_ = l_Lean_SourceInfo_fromRef(v_ref_2953_, v___x_2954_);
v___x_2956_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2957_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__277, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__277_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__277);
v___x_2958_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__279));
lean_inc(v_currMacroScope_2952_);
lean_inc(v_quotContext_2951_);
v___x_2959_ = l_Lean_addMacroScope(v_quotContext_2951_, v___x_2958_, v_currMacroScope_2952_);
v___x_2960_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__283));
lean_inc_n(v___x_2955_, 2);
v___x_2961_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2961_, 0, v___x_2955_);
lean_ctor_set(v___x_2961_, 1, v___x_2957_);
lean_ctor_set(v___x_2961_, 2, v___x_2959_);
lean_ctor_set(v___x_2961_, 3, v___x_2960_);
v___x_2962_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2963_ = l_Lean_Syntax_node1(v___x_2955_, v___x_2962_, v_a_2946_);
v___x_2964_ = l_Lean_Syntax_node2(v___x_2955_, v___x_2956_, v___x_2961_, v___x_2963_);
if (v_isShared_2950_ == 0)
{
lean_ctor_set(v___x_2949_, 0, v___x_2964_);
v___x_2966_ = v___x_2949_;
goto v_reusejp_2965_;
}
else
{
lean_object* v_reuseFailAlloc_2967_; 
v_reuseFailAlloc_2967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2967_, 0, v___x_2964_);
lean_ctor_set(v_reuseFailAlloc_2967_, 1, v_a_2947_);
v___x_2966_ = v_reuseFailAlloc_2967_;
goto v_reusejp_2965_;
}
v_reusejp_2965_:
{
return v___x_2966_;
}
}
}
case 31:
{
uint8_t v_presentation_2969_; lean_object* v___x_2970_; lean_object* v_a_2971_; lean_object* v_a_2972_; lean_object* v___x_2974_; uint8_t v_isShared_2975_; uint8_t v_isSharedCheck_2993_; 
v_presentation_2969_ = lean_ctor_get_uint8(v_x_1717_, 0);
lean_dec_ref_known(v_x_1717_, 0);
v___x_2970_ = l___private_Std_Time_Notation_0__Std_Time_convertZoneName(v_presentation_2969_, v_a_1718_, v_a_1719_);
v_a_2971_ = lean_ctor_get(v___x_2970_, 0);
v_a_2972_ = lean_ctor_get(v___x_2970_, 1);
v_isSharedCheck_2993_ = !lean_is_exclusive(v___x_2970_);
if (v_isSharedCheck_2993_ == 0)
{
v___x_2974_ = v___x_2970_;
v_isShared_2975_ = v_isSharedCheck_2993_;
goto v_resetjp_2973_;
}
else
{
lean_inc(v_a_2972_);
lean_inc(v_a_2971_);
lean_dec(v___x_2970_);
v___x_2974_ = lean_box(0);
v_isShared_2975_ = v_isSharedCheck_2993_;
goto v_resetjp_2973_;
}
v_resetjp_2973_:
{
lean_object* v_quotContext_2976_; lean_object* v_currMacroScope_2977_; lean_object* v_ref_2978_; uint8_t v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2991_; 
v_quotContext_2976_ = lean_ctor_get(v_a_1718_, 1);
v_currMacroScope_2977_ = lean_ctor_get(v_a_1718_, 2);
v_ref_2978_ = lean_ctor_get(v_a_1718_, 5);
v___x_2979_ = 0;
v___x_2980_ = l_Lean_SourceInfo_fromRef(v_ref_2978_, v___x_2979_);
v___x_2981_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2982_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__285, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__285_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__285);
v___x_2983_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__287));
lean_inc(v_currMacroScope_2977_);
lean_inc(v_quotContext_2976_);
v___x_2984_ = l_Lean_addMacroScope(v_quotContext_2976_, v___x_2983_, v_currMacroScope_2977_);
v___x_2985_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__291));
lean_inc_n(v___x_2980_, 2);
v___x_2986_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2986_, 0, v___x_2980_);
lean_ctor_set(v___x_2986_, 1, v___x_2982_);
lean_ctor_set(v___x_2986_, 2, v___x_2984_);
lean_ctor_set(v___x_2986_, 3, v___x_2985_);
v___x_2987_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2988_ = l_Lean_Syntax_node1(v___x_2980_, v___x_2987_, v_a_2971_);
v___x_2989_ = l_Lean_Syntax_node2(v___x_2980_, v___x_2981_, v___x_2986_, v___x_2988_);
if (v_isShared_2975_ == 0)
{
lean_ctor_set(v___x_2974_, 0, v___x_2989_);
v___x_2991_ = v___x_2974_;
goto v_reusejp_2990_;
}
else
{
lean_object* v_reuseFailAlloc_2992_; 
v_reuseFailAlloc_2992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2992_, 0, v___x_2989_);
lean_ctor_set(v_reuseFailAlloc_2992_, 1, v_a_2972_);
v___x_2991_ = v_reuseFailAlloc_2992_;
goto v_reusejp_2990_;
}
v_reusejp_2990_:
{
return v___x_2991_;
}
}
}
case 32:
{
uint8_t v_presentation_2994_; lean_object* v___x_2995_; lean_object* v_a_2996_; lean_object* v_a_2997_; lean_object* v___x_2999_; uint8_t v_isShared_3000_; uint8_t v_isSharedCheck_3018_; 
v_presentation_2994_ = lean_ctor_get_uint8(v_x_1717_, 0);
lean_dec_ref_known(v_x_1717_, 0);
v___x_2995_ = l___private_Std_Time_Notation_0__Std_Time_convertOffsetO(v_presentation_2994_, v_a_1718_, v_a_1719_);
v_a_2996_ = lean_ctor_get(v___x_2995_, 0);
v_a_2997_ = lean_ctor_get(v___x_2995_, 1);
v_isSharedCheck_3018_ = !lean_is_exclusive(v___x_2995_);
if (v_isSharedCheck_3018_ == 0)
{
v___x_2999_ = v___x_2995_;
v_isShared_3000_ = v_isSharedCheck_3018_;
goto v_resetjp_2998_;
}
else
{
lean_inc(v_a_2997_);
lean_inc(v_a_2996_);
lean_dec(v___x_2995_);
v___x_2999_ = lean_box(0);
v_isShared_3000_ = v_isSharedCheck_3018_;
goto v_resetjp_2998_;
}
v_resetjp_2998_:
{
lean_object* v_quotContext_3001_; lean_object* v_currMacroScope_3002_; lean_object* v_ref_3003_; uint8_t v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3016_; 
v_quotContext_3001_ = lean_ctor_get(v_a_1718_, 1);
v_currMacroScope_3002_ = lean_ctor_get(v_a_1718_, 2);
v_ref_3003_ = lean_ctor_get(v_a_1718_, 5);
v___x_3004_ = 0;
v___x_3005_ = l_Lean_SourceInfo_fromRef(v_ref_3003_, v___x_3004_);
v___x_3006_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_3007_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__293, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__293_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__293);
v___x_3008_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__295));
lean_inc(v_currMacroScope_3002_);
lean_inc(v_quotContext_3001_);
v___x_3009_ = l_Lean_addMacroScope(v_quotContext_3001_, v___x_3008_, v_currMacroScope_3002_);
v___x_3010_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__299));
lean_inc_n(v___x_3005_, 2);
v___x_3011_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3011_, 0, v___x_3005_);
lean_ctor_set(v___x_3011_, 1, v___x_3007_);
lean_ctor_set(v___x_3011_, 2, v___x_3009_);
lean_ctor_set(v___x_3011_, 3, v___x_3010_);
v___x_3012_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_3013_ = l_Lean_Syntax_node1(v___x_3005_, v___x_3012_, v_a_2996_);
v___x_3014_ = l_Lean_Syntax_node2(v___x_3005_, v___x_3006_, v___x_3011_, v___x_3013_);
if (v_isShared_3000_ == 0)
{
lean_ctor_set(v___x_2999_, 0, v___x_3014_);
v___x_3016_ = v___x_2999_;
goto v_reusejp_3015_;
}
else
{
lean_object* v_reuseFailAlloc_3017_; 
v_reuseFailAlloc_3017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3017_, 0, v___x_3014_);
lean_ctor_set(v_reuseFailAlloc_3017_, 1, v_a_2997_);
v___x_3016_ = v_reuseFailAlloc_3017_;
goto v_reusejp_3015_;
}
v_reusejp_3015_:
{
return v___x_3016_;
}
}
}
case 33:
{
uint8_t v_presentation_3019_; lean_object* v___x_3020_; lean_object* v_a_3021_; lean_object* v_a_3022_; lean_object* v___x_3024_; uint8_t v_isShared_3025_; uint8_t v_isSharedCheck_3043_; 
v_presentation_3019_ = lean_ctor_get_uint8(v_x_1717_, 0);
lean_dec_ref_known(v_x_1717_, 0);
v___x_3020_ = l___private_Std_Time_Notation_0__Std_Time_convertOffsetX(v_presentation_3019_, v_a_1718_, v_a_1719_);
v_a_3021_ = lean_ctor_get(v___x_3020_, 0);
v_a_3022_ = lean_ctor_get(v___x_3020_, 1);
v_isSharedCheck_3043_ = !lean_is_exclusive(v___x_3020_);
if (v_isSharedCheck_3043_ == 0)
{
v___x_3024_ = v___x_3020_;
v_isShared_3025_ = v_isSharedCheck_3043_;
goto v_resetjp_3023_;
}
else
{
lean_inc(v_a_3022_);
lean_inc(v_a_3021_);
lean_dec(v___x_3020_);
v___x_3024_ = lean_box(0);
v_isShared_3025_ = v_isSharedCheck_3043_;
goto v_resetjp_3023_;
}
v_resetjp_3023_:
{
lean_object* v_quotContext_3026_; lean_object* v_currMacroScope_3027_; lean_object* v_ref_3028_; uint8_t v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3041_; 
v_quotContext_3026_ = lean_ctor_get(v_a_1718_, 1);
v_currMacroScope_3027_ = lean_ctor_get(v_a_1718_, 2);
v_ref_3028_ = lean_ctor_get(v_a_1718_, 5);
v___x_3029_ = 0;
v___x_3030_ = l_Lean_SourceInfo_fromRef(v_ref_3028_, v___x_3029_);
v___x_3031_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_3032_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__301, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__301_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__301);
v___x_3033_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__303));
lean_inc(v_currMacroScope_3027_);
lean_inc(v_quotContext_3026_);
v___x_3034_ = l_Lean_addMacroScope(v_quotContext_3026_, v___x_3033_, v_currMacroScope_3027_);
v___x_3035_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__307));
lean_inc_n(v___x_3030_, 2);
v___x_3036_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3036_, 0, v___x_3030_);
lean_ctor_set(v___x_3036_, 1, v___x_3032_);
lean_ctor_set(v___x_3036_, 2, v___x_3034_);
lean_ctor_set(v___x_3036_, 3, v___x_3035_);
v___x_3037_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_3038_ = l_Lean_Syntax_node1(v___x_3030_, v___x_3037_, v_a_3021_);
v___x_3039_ = l_Lean_Syntax_node2(v___x_3030_, v___x_3031_, v___x_3036_, v___x_3038_);
if (v_isShared_3025_ == 0)
{
lean_ctor_set(v___x_3024_, 0, v___x_3039_);
v___x_3041_ = v___x_3024_;
goto v_reusejp_3040_;
}
else
{
lean_object* v_reuseFailAlloc_3042_; 
v_reuseFailAlloc_3042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3042_, 0, v___x_3039_);
lean_ctor_set(v_reuseFailAlloc_3042_, 1, v_a_3022_);
v___x_3041_ = v_reuseFailAlloc_3042_;
goto v_reusejp_3040_;
}
v_reusejp_3040_:
{
return v___x_3041_;
}
}
}
case 34:
{
uint8_t v_presentation_3044_; lean_object* v___x_3045_; lean_object* v_a_3046_; lean_object* v_a_3047_; lean_object* v___x_3049_; uint8_t v_isShared_3050_; uint8_t v_isSharedCheck_3068_; 
v_presentation_3044_ = lean_ctor_get_uint8(v_x_1717_, 0);
lean_dec_ref_known(v_x_1717_, 0);
v___x_3045_ = l___private_Std_Time_Notation_0__Std_Time_convertOffsetX(v_presentation_3044_, v_a_1718_, v_a_1719_);
v_a_3046_ = lean_ctor_get(v___x_3045_, 0);
v_a_3047_ = lean_ctor_get(v___x_3045_, 1);
v_isSharedCheck_3068_ = !lean_is_exclusive(v___x_3045_);
if (v_isSharedCheck_3068_ == 0)
{
v___x_3049_ = v___x_3045_;
v_isShared_3050_ = v_isSharedCheck_3068_;
goto v_resetjp_3048_;
}
else
{
lean_inc(v_a_3047_);
lean_inc(v_a_3046_);
lean_dec(v___x_3045_);
v___x_3049_ = lean_box(0);
v_isShared_3050_ = v_isSharedCheck_3068_;
goto v_resetjp_3048_;
}
v_resetjp_3048_:
{
lean_object* v_quotContext_3051_; lean_object* v_currMacroScope_3052_; lean_object* v_ref_3053_; uint8_t v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3066_; 
v_quotContext_3051_ = lean_ctor_get(v_a_1718_, 1);
v_currMacroScope_3052_ = lean_ctor_get(v_a_1718_, 2);
v_ref_3053_ = lean_ctor_get(v_a_1718_, 5);
v___x_3054_ = 0;
v___x_3055_ = l_Lean_SourceInfo_fromRef(v_ref_3053_, v___x_3054_);
v___x_3056_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_3057_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__309, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__309_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__309);
v___x_3058_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__311));
lean_inc(v_currMacroScope_3052_);
lean_inc(v_quotContext_3051_);
v___x_3059_ = l_Lean_addMacroScope(v_quotContext_3051_, v___x_3058_, v_currMacroScope_3052_);
v___x_3060_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__315));
lean_inc_n(v___x_3055_, 2);
v___x_3061_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3061_, 0, v___x_3055_);
lean_ctor_set(v___x_3061_, 1, v___x_3057_);
lean_ctor_set(v___x_3061_, 2, v___x_3059_);
lean_ctor_set(v___x_3061_, 3, v___x_3060_);
v___x_3062_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_3063_ = l_Lean_Syntax_node1(v___x_3055_, v___x_3062_, v_a_3046_);
v___x_3064_ = l_Lean_Syntax_node2(v___x_3055_, v___x_3056_, v___x_3061_, v___x_3063_);
if (v_isShared_3050_ == 0)
{
lean_ctor_set(v___x_3049_, 0, v___x_3064_);
v___x_3066_ = v___x_3049_;
goto v_reusejp_3065_;
}
else
{
lean_object* v_reuseFailAlloc_3067_; 
v_reuseFailAlloc_3067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3067_, 0, v___x_3064_);
lean_ctor_set(v_reuseFailAlloc_3067_, 1, v_a_3047_);
v___x_3066_ = v_reuseFailAlloc_3067_;
goto v_reusejp_3065_;
}
v_reusejp_3065_:
{
return v___x_3066_;
}
}
}
default: 
{
uint8_t v_presentation_3069_; lean_object* v___x_3070_; lean_object* v_a_3071_; lean_object* v_a_3072_; lean_object* v___x_3074_; uint8_t v_isShared_3075_; uint8_t v_isSharedCheck_3093_; 
v_presentation_3069_ = lean_ctor_get_uint8(v_x_1717_, 0);
lean_dec_ref_known(v_x_1717_, 0);
v___x_3070_ = l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ(v_presentation_3069_, v_a_1718_, v_a_1719_);
v_a_3071_ = lean_ctor_get(v___x_3070_, 0);
v_a_3072_ = lean_ctor_get(v___x_3070_, 1);
v_isSharedCheck_3093_ = !lean_is_exclusive(v___x_3070_);
if (v_isSharedCheck_3093_ == 0)
{
v___x_3074_ = v___x_3070_;
v_isShared_3075_ = v_isSharedCheck_3093_;
goto v_resetjp_3073_;
}
else
{
lean_inc(v_a_3072_);
lean_inc(v_a_3071_);
lean_dec(v___x_3070_);
v___x_3074_ = lean_box(0);
v_isShared_3075_ = v_isSharedCheck_3093_;
goto v_resetjp_3073_;
}
v_resetjp_3073_:
{
lean_object* v_quotContext_3076_; lean_object* v_currMacroScope_3077_; lean_object* v_ref_3078_; uint8_t v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3091_; 
v_quotContext_3076_ = lean_ctor_get(v_a_1718_, 1);
v_currMacroScope_3077_ = lean_ctor_get(v_a_1718_, 2);
v_ref_3078_ = lean_ctor_get(v_a_1718_, 5);
v___x_3079_ = 0;
v___x_3080_ = l_Lean_SourceInfo_fromRef(v_ref_3078_, v___x_3079_);
v___x_3081_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_3082_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__317, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__317_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__317);
v___x_3083_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__319));
lean_inc(v_currMacroScope_3077_);
lean_inc(v_quotContext_3076_);
v___x_3084_ = l_Lean_addMacroScope(v_quotContext_3076_, v___x_3083_, v_currMacroScope_3077_);
v___x_3085_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__323));
lean_inc_n(v___x_3080_, 2);
v___x_3086_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3086_, 0, v___x_3080_);
lean_ctor_set(v___x_3086_, 1, v___x_3082_);
lean_ctor_set(v___x_3086_, 2, v___x_3084_);
lean_ctor_set(v___x_3086_, 3, v___x_3085_);
v___x_3087_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_3088_ = l_Lean_Syntax_node1(v___x_3080_, v___x_3087_, v_a_3071_);
v___x_3089_ = l_Lean_Syntax_node2(v___x_3080_, v___x_3081_, v___x_3086_, v___x_3088_);
if (v_isShared_3075_ == 0)
{
lean_ctor_set(v___x_3074_, 0, v___x_3089_);
v___x_3091_ = v___x_3074_;
goto v_reusejp_3090_;
}
else
{
lean_object* v_reuseFailAlloc_3092_; 
v_reuseFailAlloc_3092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3092_, 0, v___x_3089_);
lean_ctor_set(v_reuseFailAlloc_3092_, 1, v_a_3072_);
v___x_3091_ = v_reuseFailAlloc_3092_;
goto v_reusejp_3090_;
}
v_reusejp_3090_:
{
return v___x_3091_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___boxed(lean_object* v_x_3094_, lean_object* v_a_3095_, lean_object* v_a_3096_){
_start:
{
lean_object* v_res_3097_; 
v_res_3097_ = l___private_Std_Time_Notation_0__Std_Time_convertModifier(v_x_3094_, v_a_3095_, v_a_3096_);
lean_dec_ref(v_a_3095_);
return v_res_3097_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertFormatPart___closed__1(void){
_start:
{
lean_object* v___x_3099_; lean_object* v___x_3100_; 
v___x_3099_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertFormatPart___closed__0));
v___x_3100_ = l_String_toRawSubstring_x27(v___x_3099_);
return v___x_3100_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertFormatPart___closed__4(void){
_start:
{
lean_object* v___x_3104_; lean_object* v___x_3105_; 
v___x_3104_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertFormatPart___closed__3));
v___x_3105_ = l_String_toRawSubstring_x27(v___x_3104_);
return v___x_3105_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertFormatPart(lean_object* v_x_3108_, lean_object* v_a_3109_, lean_object* v_a_3110_){
_start:
{
if (lean_obj_tag(v_x_3108_) == 0)
{
lean_object* v_val_3111_; lean_object* v_quotContext_3112_; lean_object* v_currMacroScope_3113_; lean_object* v_ref_3114_; uint8_t v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; 
v_val_3111_ = lean_ctor_get(v_x_3108_, 0);
lean_inc_ref(v_val_3111_);
lean_dec_ref_known(v_x_3108_, 1);
v_quotContext_3112_ = lean_ctor_get(v_a_3109_, 1);
v_currMacroScope_3113_ = lean_ctor_get(v_a_3109_, 2);
v_ref_3114_ = lean_ctor_get(v_a_3109_, 5);
v___x_3115_ = 0;
v___x_3116_ = l_Lean_SourceInfo_fromRef(v_ref_3114_, v___x_3115_);
v___x_3117_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_3118_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__67));
v___x_3119_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__68));
lean_inc_n(v___x_3116_, 4);
v___x_3120_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3120_, 0, v___x_3116_);
lean_ctor_set(v___x_3120_, 1, v___x_3119_);
v___x_3121_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertFormatPart___closed__1, &l___private_Std_Time_Notation_0__Std_Time_convertFormatPart___closed__1_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertFormatPart___closed__1);
v___x_3122_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertFormatPart___closed__2));
lean_inc(v_currMacroScope_3113_);
lean_inc(v_quotContext_3112_);
v___x_3123_ = l_Lean_addMacroScope(v_quotContext_3112_, v___x_3122_, v_currMacroScope_3113_);
v___x_3124_ = lean_box(0);
v___x_3125_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3125_, 0, v___x_3116_);
lean_ctor_set(v___x_3125_, 1, v___x_3121_);
lean_ctor_set(v___x_3125_, 2, v___x_3123_);
lean_ctor_set(v___x_3125_, 3, v___x_3124_);
v___x_3126_ = l_Lean_Syntax_node2(v___x_3116_, v___x_3118_, v___x_3120_, v___x_3125_);
v___x_3127_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_3128_ = lean_box(2);
v___x_3129_ = l_Lean_Syntax_mkStrLit(v_val_3111_, v___x_3128_);
v___x_3130_ = l_Lean_Syntax_node1(v___x_3116_, v___x_3127_, v___x_3129_);
v___x_3131_ = l_Lean_Syntax_node2(v___x_3116_, v___x_3117_, v___x_3126_, v___x_3130_);
v___x_3132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3132_, 0, v___x_3131_);
lean_ctor_set(v___x_3132_, 1, v_a_3110_);
return v___x_3132_;
}
else
{
lean_object* v_modifier_3133_; lean_object* v___x_3134_; lean_object* v_a_3135_; lean_object* v_a_3136_; lean_object* v___x_3138_; uint8_t v_isShared_3139_; uint8_t v_isSharedCheck_3161_; 
v_modifier_3133_ = lean_ctor_get(v_x_3108_, 0);
lean_inc_ref(v_modifier_3133_);
lean_dec_ref_known(v_x_3108_, 1);
v___x_3134_ = l___private_Std_Time_Notation_0__Std_Time_convertModifier(v_modifier_3133_, v_a_3109_, v_a_3110_);
v_a_3135_ = lean_ctor_get(v___x_3134_, 0);
v_a_3136_ = lean_ctor_get(v___x_3134_, 1);
v_isSharedCheck_3161_ = !lean_is_exclusive(v___x_3134_);
if (v_isSharedCheck_3161_ == 0)
{
v___x_3138_ = v___x_3134_;
v_isShared_3139_ = v_isSharedCheck_3161_;
goto v_resetjp_3137_;
}
else
{
lean_inc(v_a_3136_);
lean_inc(v_a_3135_);
lean_dec(v___x_3134_);
v___x_3138_ = lean_box(0);
v_isShared_3139_ = v_isSharedCheck_3161_;
goto v_resetjp_3137_;
}
v_resetjp_3137_:
{
lean_object* v_quotContext_3140_; lean_object* v_currMacroScope_3141_; lean_object* v_ref_3142_; uint8_t v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3159_; 
v_quotContext_3140_ = lean_ctor_get(v_a_3109_, 1);
v_currMacroScope_3141_ = lean_ctor_get(v_a_3109_, 2);
v_ref_3142_ = lean_ctor_get(v_a_3109_, 5);
v___x_3143_ = 0;
v___x_3144_ = l_Lean_SourceInfo_fromRef(v_ref_3142_, v___x_3143_);
v___x_3145_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_3146_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__67));
v___x_3147_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__68));
lean_inc_n(v___x_3144_, 4);
v___x_3148_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3148_, 0, v___x_3144_);
lean_ctor_set(v___x_3148_, 1, v___x_3147_);
v___x_3149_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertFormatPart___closed__4, &l___private_Std_Time_Notation_0__Std_Time_convertFormatPart___closed__4_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertFormatPart___closed__4);
v___x_3150_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertFormatPart___closed__5));
lean_inc(v_currMacroScope_3141_);
lean_inc(v_quotContext_3140_);
v___x_3151_ = l_Lean_addMacroScope(v_quotContext_3140_, v___x_3150_, v_currMacroScope_3141_);
v___x_3152_ = lean_box(0);
v___x_3153_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3153_, 0, v___x_3144_);
lean_ctor_set(v___x_3153_, 1, v___x_3149_);
lean_ctor_set(v___x_3153_, 2, v___x_3151_);
lean_ctor_set(v___x_3153_, 3, v___x_3152_);
v___x_3154_ = l_Lean_Syntax_node2(v___x_3144_, v___x_3146_, v___x_3148_, v___x_3153_);
v___x_3155_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_3156_ = l_Lean_Syntax_node1(v___x_3144_, v___x_3155_, v_a_3135_);
v___x_3157_ = l_Lean_Syntax_node2(v___x_3144_, v___x_3145_, v___x_3154_, v___x_3156_);
if (v_isShared_3139_ == 0)
{
lean_ctor_set(v___x_3138_, 0, v___x_3157_);
v___x_3159_ = v___x_3138_;
goto v_reusejp_3158_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3160_, 0, v___x_3157_);
lean_ctor_set(v_reuseFailAlloc_3160_, 1, v_a_3136_);
v___x_3159_ = v_reuseFailAlloc_3160_;
goto v_reusejp_3158_;
}
v_reusejp_3158_:
{
return v___x_3159_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertFormatPart___boxed(lean_object* v_x_3162_, lean_object* v_a_3163_, lean_object* v_a_3164_){
_start:
{
lean_object* v_res_3165_; 
v_res_3165_ = l___private_Std_Time_Notation_0__Std_Time_convertFormatPart(v_x_3162_, v_a_3163_, v_a_3164_);
lean_dec_ref(v_a_3163_);
return v_res_3165_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxNat(lean_object* v_n_3169_, lean_object* v_a_3170_, lean_object* v_a_3171_){
_start:
{
lean_object* v_ref_3172_; uint8_t v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; 
v_ref_3172_ = lean_ctor_get(v_a_3170_, 5);
v___x_3173_ = 0;
v___x_3174_ = l_Lean_SourceInfo_fromRef(v_ref_3172_, v___x_3173_);
v___x_3175_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxNat___closed__1));
v___x_3176_ = l_Nat_reprFast(v_n_3169_);
lean_inc(v___x_3174_);
v___x_3177_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3177_, 0, v___x_3174_);
lean_ctor_set(v___x_3177_, 1, v___x_3176_);
v___x_3178_ = l_Lean_Syntax_node1(v___x_3174_, v___x_3175_, v___x_3177_);
v___x_3179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3179_, 0, v___x_3178_);
lean_ctor_set(v___x_3179_, 1, v_a_3171_);
return v___x_3179_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxNat___boxed(lean_object* v_n_3180_, lean_object* v_a_3181_, lean_object* v_a_3182_){
_start:
{
lean_object* v_res_3183_; 
v_res_3183_ = l___private_Std_Time_Notation_0__Std_Time_syntaxNat(v_n_3180_, v_a_3181_, v_a_3182_);
lean_dec_ref(v_a_3181_);
return v_res_3183_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxString(lean_object* v_n_3187_, lean_object* v_a_3188_, lean_object* v_a_3189_){
_start:
{
lean_object* v_ref_3190_; uint8_t v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; 
v_ref_3190_ = lean_ctor_get(v_a_3188_, 5);
v___x_3191_ = 0;
v___x_3192_ = l_Lean_SourceInfo_fromRef(v_ref_3190_, v___x_3191_);
v___x_3193_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxString___closed__1));
lean_inc(v___x_3192_);
v___x_3194_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3194_, 0, v___x_3192_);
lean_ctor_set(v___x_3194_, 1, v_n_3187_);
v___x_3195_ = l_Lean_Syntax_node1(v___x_3192_, v___x_3193_, v___x_3194_);
v___x_3196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3196_, 0, v___x_3195_);
lean_ctor_set(v___x_3196_, 1, v_a_3189_);
return v___x_3196_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxString___boxed(lean_object* v_n_3197_, lean_object* v_a_3198_, lean_object* v_a_3199_){
_start:
{
lean_object* v_res_3200_; 
v_res_3200_ = l___private_Std_Time_Notation_0__Std_Time_syntaxString(v_n_3197_, v_a_3198_, v_a_3199_);
lean_dec_ref(v_a_3198_);
return v_res_3200_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__0(void){
_start:
{
lean_object* v_natZero_3201_; lean_object* v_intZero_3202_; 
v_natZero_3201_ = lean_unsigned_to_nat(0u);
v_intZero_3202_ = lean_nat_to_int(v_natZero_3201_);
return v_intZero_3202_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__2(void){
_start:
{
lean_object* v___x_3204_; lean_object* v___x_3205_; 
v___x_3204_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__1));
v___x_3205_ = l_String_toRawSubstring_x27(v___x_3204_);
return v___x_3205_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__11(void){
_start:
{
lean_object* v___x_3223_; lean_object* v___x_3224_; 
v___x_3223_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__10));
v___x_3224_ = l_String_toRawSubstring_x27(v___x_3223_);
return v___x_3224_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxInt(lean_object* v_n_3240_, lean_object* v_a_3241_, lean_object* v_a_3242_){
_start:
{
lean_object* v_intZero_3243_; uint8_t v_isNeg_3244_; 
v_intZero_3243_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__0, &l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__0_once, _init_l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__0);
v_isNeg_3244_ = lean_int_dec_lt(v_n_3240_, v_intZero_3243_);
if (v_isNeg_3244_ == 0)
{
lean_object* v_quotContext_3245_; lean_object* v_currMacroScope_3246_; lean_object* v_ref_3247_; lean_object* v_a_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; 
v_quotContext_3245_ = lean_ctor_get(v_a_3241_, 1);
v_currMacroScope_3246_ = lean_ctor_get(v_a_3241_, 2);
v_ref_3247_ = lean_ctor_get(v_a_3241_, 5);
v_a_3248_ = lean_nat_abs(v_n_3240_);
v___x_3249_ = l_Lean_SourceInfo_fromRef(v_ref_3247_, v_isNeg_3244_);
v___x_3250_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_3251_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__2, &l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__2_once, _init_l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__2);
v___x_3252_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__5));
lean_inc(v_currMacroScope_3246_);
lean_inc(v_quotContext_3245_);
v___x_3253_ = l_Lean_addMacroScope(v_quotContext_3245_, v___x_3252_, v_currMacroScope_3246_);
v___x_3254_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__9));
lean_inc_n(v___x_3249_, 2);
v___x_3255_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3255_, 0, v___x_3249_);
lean_ctor_set(v___x_3255_, 1, v___x_3251_);
lean_ctor_set(v___x_3255_, 2, v___x_3253_);
lean_ctor_set(v___x_3255_, 3, v___x_3254_);
v___x_3256_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_3257_ = l_Nat_reprFast(v_a_3248_);
v___x_3258_ = lean_box(2);
v___x_3259_ = l_Lean_Syntax_mkNumLit(v___x_3257_, v___x_3258_);
v___x_3260_ = l_Lean_Syntax_node1(v___x_3249_, v___x_3256_, v___x_3259_);
v___x_3261_ = l_Lean_Syntax_node2(v___x_3249_, v___x_3250_, v___x_3255_, v___x_3260_);
v___x_3262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3262_, 0, v___x_3261_);
lean_ctor_set(v___x_3262_, 1, v_a_3242_);
return v___x_3262_;
}
else
{
lean_object* v_quotContext_3263_; lean_object* v_currMacroScope_3264_; lean_object* v_ref_3265_; lean_object* v_abs_3266_; lean_object* v_one_3267_; lean_object* v_a_3268_; uint8_t v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; 
v_quotContext_3263_ = lean_ctor_get(v_a_3241_, 1);
v_currMacroScope_3264_ = lean_ctor_get(v_a_3241_, 2);
v_ref_3265_ = lean_ctor_get(v_a_3241_, 5);
v_abs_3266_ = lean_nat_abs(v_n_3240_);
v_one_3267_ = lean_unsigned_to_nat(1u);
v_a_3268_ = lean_nat_sub(v_abs_3266_, v_one_3267_);
lean_dec(v_abs_3266_);
v___x_3269_ = 0;
v___x_3270_ = l_Lean_SourceInfo_fromRef(v_ref_3265_, v___x_3269_);
v___x_3271_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_3272_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__11, &l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__11_once, _init_l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__11);
v___x_3273_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__13));
lean_inc(v_currMacroScope_3264_);
lean_inc(v_quotContext_3263_);
v___x_3274_ = l_Lean_addMacroScope(v_quotContext_3263_, v___x_3273_, v_currMacroScope_3264_);
v___x_3275_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__17));
lean_inc_n(v___x_3270_, 2);
v___x_3276_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3276_, 0, v___x_3270_);
lean_ctor_set(v___x_3276_, 1, v___x_3272_);
lean_ctor_set(v___x_3276_, 2, v___x_3274_);
lean_ctor_set(v___x_3276_, 3, v___x_3275_);
v___x_3277_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_3278_ = l_Nat_reprFast(v_a_3268_);
v___x_3279_ = lean_box(2);
v___x_3280_ = l_Lean_Syntax_mkNumLit(v___x_3278_, v___x_3279_);
v___x_3281_ = l_Lean_Syntax_node1(v___x_3270_, v___x_3277_, v___x_3280_);
v___x_3282_ = l_Lean_Syntax_node2(v___x_3270_, v___x_3271_, v___x_3276_, v___x_3281_);
v___x_3283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3283_, 0, v___x_3282_);
lean_ctor_set(v___x_3283_, 1, v_a_3242_);
return v___x_3283_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxInt___boxed(lean_object* v_n_3284_, lean_object* v_a_3285_, lean_object* v_a_3286_){
_start:
{
lean_object* v_res_3287_; 
v_res_3287_ = l___private_Std_Time_Notation_0__Std_Time_syntaxInt(v_n_3284_, v_a_3285_, v_a_3286_);
lean_dec_ref(v_a_3285_);
lean_dec(v_n_3284_);
return v_res_3287_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__1(void){
_start:
{
lean_object* v___x_3289_; lean_object* v___x_3290_; 
v___x_3289_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__0));
v___x_3290_ = l_String_toRawSubstring_x27(v___x_3289_);
return v___x_3290_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__21(void){
_start:
{
lean_object* v___x_3340_; 
v___x_3340_ = l_Array_mkArray0___redArg();
return v___x_3340_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxBounded(lean_object* v_n_3341_, lean_object* v_a_3342_, lean_object* v_a_3343_){
_start:
{
lean_object* v___x_3344_; lean_object* v_a_3345_; lean_object* v_a_3346_; lean_object* v___x_3348_; uint8_t v_isShared_3349_; uint8_t v_isSharedCheck_3399_; 
v___x_3344_ = l___private_Std_Time_Notation_0__Std_Time_syntaxInt(v_n_3341_, v_a_3342_, v_a_3343_);
v_a_3345_ = lean_ctor_get(v___x_3344_, 0);
v_a_3346_ = lean_ctor_get(v___x_3344_, 1);
v_isSharedCheck_3399_ = !lean_is_exclusive(v___x_3344_);
if (v_isSharedCheck_3399_ == 0)
{
v___x_3348_ = v___x_3344_;
v_isShared_3349_ = v_isSharedCheck_3399_;
goto v_resetjp_3347_;
}
else
{
lean_inc(v_a_3346_);
lean_inc(v_a_3345_);
lean_dec(v___x_3344_);
v___x_3348_ = lean_box(0);
v_isShared_3349_ = v_isSharedCheck_3399_;
goto v_resetjp_3347_;
}
v_resetjp_3347_:
{
lean_object* v_quotContext_3350_; lean_object* v_currMacroScope_3351_; lean_object* v_ref_3352_; uint8_t v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3397_; 
v_quotContext_3350_ = lean_ctor_get(v_a_3342_, 1);
v_currMacroScope_3351_ = lean_ctor_get(v_a_3342_, 2);
v_ref_3352_ = lean_ctor_get(v_a_3342_, 5);
v___x_3353_ = 0;
v___x_3354_ = l_Lean_SourceInfo_fromRef(v_ref_3352_, v___x_3353_);
v___x_3355_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_3356_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__1, &l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__1_once, _init_l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__1);
v___x_3357_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__6));
lean_inc_n(v_currMacroScope_3351_, 2);
lean_inc_n(v_quotContext_3350_, 2);
v___x_3358_ = l_Lean_addMacroScope(v_quotContext_3350_, v___x_3357_, v_currMacroScope_3351_);
v___x_3359_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__8));
lean_inc_n(v___x_3354_, 17);
v___x_3360_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3360_, 0, v___x_3354_);
lean_ctor_set(v___x_3360_, 1, v___x_3356_);
lean_ctor_set(v___x_3360_, 2, v___x_3358_);
lean_ctor_set(v___x_3360_, 3, v___x_3359_);
v___x_3361_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_3362_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__42));
v___x_3363_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__44));
v___x_3364_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__45));
v___x_3365_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3365_, 0, v___x_3354_);
lean_ctor_set(v___x_3365_, 1, v___x_3364_);
v___x_3366_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__47));
v___x_3367_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49);
v___x_3368_ = lean_box(0);
v___x_3369_ = l_Lean_addMacroScope(v_quotContext_3350_, v___x_3368_, v_currMacroScope_3351_);
v___x_3370_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__65));
v___x_3371_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3371_, 0, v___x_3354_);
lean_ctor_set(v___x_3371_, 1, v___x_3367_);
lean_ctor_set(v___x_3371_, 2, v___x_3369_);
lean_ctor_set(v___x_3371_, 3, v___x_3370_);
v___x_3372_ = l_Lean_Syntax_node1(v___x_3354_, v___x_3366_, v___x_3371_);
v___x_3373_ = l_Lean_Syntax_node2(v___x_3354_, v___x_3363_, v___x_3365_, v___x_3372_);
v___x_3374_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__10));
v___x_3375_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__11));
v___x_3376_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3376_, 0, v___x_3354_);
lean_ctor_set(v___x_3376_, 1, v___x_3375_);
v___x_3377_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__14));
v___x_3378_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__16));
v___x_3379_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__17));
v___x_3380_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__18));
v___x_3381_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3381_, 0, v___x_3354_);
lean_ctor_set(v___x_3381_, 1, v___x_3379_);
v___x_3382_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__20));
v___x_3383_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__21, &l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__21_once, _init_l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__21);
v___x_3384_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3384_, 0, v___x_3354_);
lean_ctor_set(v___x_3384_, 1, v___x_3361_);
lean_ctor_set(v___x_3384_, 2, v___x_3383_);
v___x_3385_ = l_Lean_Syntax_node1(v___x_3354_, v___x_3382_, v___x_3384_);
v___x_3386_ = l_Lean_Syntax_node2(v___x_3354_, v___x_3380_, v___x_3381_, v___x_3385_);
v___x_3387_ = l_Lean_Syntax_node1(v___x_3354_, v___x_3361_, v___x_3386_);
v___x_3388_ = l_Lean_Syntax_node1(v___x_3354_, v___x_3378_, v___x_3387_);
v___x_3389_ = l_Lean_Syntax_node1(v___x_3354_, v___x_3377_, v___x_3388_);
v___x_3390_ = l_Lean_Syntax_node2(v___x_3354_, v___x_3374_, v___x_3376_, v___x_3389_);
v___x_3391_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__72));
v___x_3392_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3392_, 0, v___x_3354_);
lean_ctor_set(v___x_3392_, 1, v___x_3391_);
v___x_3393_ = l_Lean_Syntax_node3(v___x_3354_, v___x_3362_, v___x_3373_, v___x_3390_, v___x_3392_);
v___x_3394_ = l_Lean_Syntax_node2(v___x_3354_, v___x_3361_, v_a_3345_, v___x_3393_);
v___x_3395_ = l_Lean_Syntax_node2(v___x_3354_, v___x_3355_, v___x_3360_, v___x_3394_);
if (v_isShared_3349_ == 0)
{
lean_ctor_set(v___x_3348_, 0, v___x_3395_);
v___x_3397_ = v___x_3348_;
goto v_reusejp_3396_;
}
else
{
lean_object* v_reuseFailAlloc_3398_; 
v_reuseFailAlloc_3398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3398_, 0, v___x_3395_);
lean_ctor_set(v_reuseFailAlloc_3398_, 1, v_a_3346_);
v___x_3397_ = v_reuseFailAlloc_3398_;
goto v_reusejp_3396_;
}
v_reusejp_3396_:
{
return v___x_3397_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___boxed(lean_object* v_n_3400_, lean_object* v_a_3401_, lean_object* v_a_3402_){
_start:
{
lean_object* v_res_3403_; 
v_res_3403_ = l___private_Std_Time_Notation_0__Std_Time_syntaxBounded(v_n_3400_, v_a_3401_, v_a_3402_);
lean_dec_ref(v_a_3401_);
lean_dec(v_n_3400_);
return v_res_3403_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_syntaxVal___closed__1(void){
_start:
{
lean_object* v___x_3405_; lean_object* v___x_3406_; 
v___x_3405_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxVal___closed__0));
v___x_3406_ = l_String_toRawSubstring_x27(v___x_3405_);
return v___x_3406_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxVal(lean_object* v_n_3426_, lean_object* v_a_3427_, lean_object* v_a_3428_){
_start:
{
lean_object* v___x_3429_; lean_object* v_a_3430_; lean_object* v_a_3431_; lean_object* v___x_3433_; uint8_t v_isShared_3434_; uint8_t v_isSharedCheck_3452_; 
v___x_3429_ = l___private_Std_Time_Notation_0__Std_Time_syntaxInt(v_n_3426_, v_a_3427_, v_a_3428_);
v_a_3430_ = lean_ctor_get(v___x_3429_, 0);
v_a_3431_ = lean_ctor_get(v___x_3429_, 1);
v_isSharedCheck_3452_ = !lean_is_exclusive(v___x_3429_);
if (v_isSharedCheck_3452_ == 0)
{
v___x_3433_ = v___x_3429_;
v_isShared_3434_ = v_isSharedCheck_3452_;
goto v_resetjp_3432_;
}
else
{
lean_inc(v_a_3431_);
lean_inc(v_a_3430_);
lean_dec(v___x_3429_);
v___x_3433_ = lean_box(0);
v_isShared_3434_ = v_isSharedCheck_3452_;
goto v_resetjp_3432_;
}
v_resetjp_3432_:
{
lean_object* v_quotContext_3435_; lean_object* v_currMacroScope_3436_; lean_object* v_ref_3437_; uint8_t v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3450_; 
v_quotContext_3435_ = lean_ctor_get(v_a_3427_, 1);
v_currMacroScope_3436_ = lean_ctor_get(v_a_3427_, 2);
v_ref_3437_ = lean_ctor_get(v_a_3427_, 5);
v___x_3438_ = 0;
v___x_3439_ = l_Lean_SourceInfo_fromRef(v_ref_3437_, v___x_3438_);
v___x_3440_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_3441_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_syntaxVal___closed__1, &l___private_Std_Time_Notation_0__Std_Time_syntaxVal___closed__1_once, _init_l___private_Std_Time_Notation_0__Std_Time_syntaxVal___closed__1);
v___x_3442_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxVal___closed__4));
lean_inc(v_currMacroScope_3436_);
lean_inc(v_quotContext_3435_);
v___x_3443_ = l_Lean_addMacroScope(v_quotContext_3435_, v___x_3442_, v_currMacroScope_3436_);
v___x_3444_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxVal___closed__8));
lean_inc_n(v___x_3439_, 2);
v___x_3445_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3445_, 0, v___x_3439_);
lean_ctor_set(v___x_3445_, 1, v___x_3441_);
lean_ctor_set(v___x_3445_, 2, v___x_3443_);
lean_ctor_set(v___x_3445_, 3, v___x_3444_);
v___x_3446_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_3447_ = l_Lean_Syntax_node1(v___x_3439_, v___x_3446_, v_a_3430_);
v___x_3448_ = l_Lean_Syntax_node2(v___x_3439_, v___x_3440_, v___x_3445_, v___x_3447_);
if (v_isShared_3434_ == 0)
{
lean_ctor_set(v___x_3433_, 0, v___x_3448_);
v___x_3450_ = v___x_3433_;
goto v_reusejp_3449_;
}
else
{
lean_object* v_reuseFailAlloc_3451_; 
v_reuseFailAlloc_3451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3451_, 0, v___x_3448_);
lean_ctor_set(v_reuseFailAlloc_3451_, 1, v_a_3431_);
v___x_3450_ = v_reuseFailAlloc_3451_;
goto v_reusejp_3449_;
}
v_reusejp_3449_:
{
return v___x_3450_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxVal___boxed(lean_object* v_n_3453_, lean_object* v_a_3454_, lean_object* v_a_3455_){
_start:
{
lean_object* v_res_3456_; 
v_res_3456_ = l___private_Std_Time_Notation_0__Std_Time_syntaxVal(v_n_3453_, v_a_3454_, v_a_3455_);
lean_dec_ref(v_a_3454_);
lean_dec(v_n_3453_);
return v_res_3456_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertOffset___closed__1(void){
_start:
{
lean_object* v___x_3458_; lean_object* v___x_3459_; 
v___x_3458_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffset___closed__0));
v___x_3459_ = l_String_toRawSubstring_x27(v___x_3458_);
return v___x_3459_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffset(lean_object* v_offset_3480_, lean_object* v_a_3481_, lean_object* v_a_3482_){
_start:
{
lean_object* v___x_3483_; lean_object* v_a_3484_; lean_object* v_a_3485_; lean_object* v___x_3487_; uint8_t v_isShared_3488_; uint8_t v_isSharedCheck_3506_; 
v___x_3483_ = l___private_Std_Time_Notation_0__Std_Time_syntaxVal(v_offset_3480_, v_a_3481_, v_a_3482_);
v_a_3484_ = lean_ctor_get(v___x_3483_, 0);
v_a_3485_ = lean_ctor_get(v___x_3483_, 1);
v_isSharedCheck_3506_ = !lean_is_exclusive(v___x_3483_);
if (v_isSharedCheck_3506_ == 0)
{
v___x_3487_ = v___x_3483_;
v_isShared_3488_ = v_isSharedCheck_3506_;
goto v_resetjp_3486_;
}
else
{
lean_inc(v_a_3485_);
lean_inc(v_a_3484_);
lean_dec(v___x_3483_);
v___x_3487_ = lean_box(0);
v_isShared_3488_ = v_isSharedCheck_3506_;
goto v_resetjp_3486_;
}
v_resetjp_3486_:
{
lean_object* v_quotContext_3489_; lean_object* v_currMacroScope_3490_; lean_object* v_ref_3491_; uint8_t v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3504_; 
v_quotContext_3489_ = lean_ctor_get(v_a_3481_, 1);
v_currMacroScope_3490_ = lean_ctor_get(v_a_3481_, 2);
v_ref_3491_ = lean_ctor_get(v_a_3481_, 5);
v___x_3492_ = 0;
v___x_3493_ = l_Lean_SourceInfo_fromRef(v_ref_3491_, v___x_3492_);
v___x_3494_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_3495_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertOffset___closed__1, &l___private_Std_Time_Notation_0__Std_Time_convertOffset___closed__1_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertOffset___closed__1);
v___x_3496_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffset___closed__5));
lean_inc(v_currMacroScope_3490_);
lean_inc(v_quotContext_3489_);
v___x_3497_ = l_Lean_addMacroScope(v_quotContext_3489_, v___x_3496_, v_currMacroScope_3490_);
v___x_3498_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffset___closed__9));
lean_inc_n(v___x_3493_, 2);
v___x_3499_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3499_, 0, v___x_3493_);
lean_ctor_set(v___x_3499_, 1, v___x_3495_);
lean_ctor_set(v___x_3499_, 2, v___x_3497_);
lean_ctor_set(v___x_3499_, 3, v___x_3498_);
v___x_3500_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_3501_ = l_Lean_Syntax_node1(v___x_3493_, v___x_3500_, v_a_3484_);
v___x_3502_ = l_Lean_Syntax_node2(v___x_3493_, v___x_3494_, v___x_3499_, v___x_3501_);
if (v_isShared_3488_ == 0)
{
lean_ctor_set(v___x_3487_, 0, v___x_3502_);
v___x_3504_ = v___x_3487_;
goto v_reusejp_3503_;
}
else
{
lean_object* v_reuseFailAlloc_3505_; 
v_reuseFailAlloc_3505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3505_, 0, v___x_3502_);
lean_ctor_set(v_reuseFailAlloc_3505_, 1, v_a_3485_);
v___x_3504_ = v_reuseFailAlloc_3505_;
goto v_reusejp_3503_;
}
v_reusejp_3503_:
{
return v___x_3504_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffset___boxed(lean_object* v_offset_3507_, lean_object* v_a_3508_, lean_object* v_a_3509_){
_start:
{
lean_object* v_res_3510_; 
v_res_3510_ = l___private_Std_Time_Notation_0__Std_Time_convertOffset(v_offset_3507_, v_a_3508_, v_a_3509_);
lean_dec_ref(v_a_3508_);
lean_dec(v_offset_3507_);
return v_res_3510_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__1(void){
_start:
{
lean_object* v___x_3512_; lean_object* v___x_3513_; 
v___x_3512_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__0));
v___x_3513_ = l_String_toRawSubstring_x27(v___x_3512_);
return v___x_3513_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__8(void){
_start:
{
lean_object* v___x_3531_; lean_object* v___x_3532_; 
v___x_3531_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__7));
v___x_3532_ = l_String_toRawSubstring_x27(v___x_3531_);
return v___x_3532_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertTimezone(lean_object* v_tz_3545_, lean_object* v_a_3546_, lean_object* v_a_3547_){
_start:
{
lean_object* v_offset_3548_; lean_object* v_name_3549_; lean_object* v_abbreviation_3550_; lean_object* v___x_3551_; lean_object* v_a_3552_; lean_object* v_a_3553_; lean_object* v___x_3555_; uint8_t v_isShared_3556_; uint8_t v_isSharedCheck_3582_; 
v_offset_3548_ = lean_ctor_get(v_tz_3545_, 0);
lean_inc(v_offset_3548_);
v_name_3549_ = lean_ctor_get(v_tz_3545_, 1);
lean_inc_ref(v_name_3549_);
v_abbreviation_3550_ = lean_ctor_get(v_tz_3545_, 2);
lean_inc_ref(v_abbreviation_3550_);
lean_dec_ref(v_tz_3545_);
v___x_3551_ = l___private_Std_Time_Notation_0__Std_Time_convertOffset(v_offset_3548_, v_a_3546_, v_a_3547_);
lean_dec(v_offset_3548_);
v_a_3552_ = lean_ctor_get(v___x_3551_, 0);
v_a_3553_ = lean_ctor_get(v___x_3551_, 1);
v_isSharedCheck_3582_ = !lean_is_exclusive(v___x_3551_);
if (v_isSharedCheck_3582_ == 0)
{
v___x_3555_ = v___x_3551_;
v_isShared_3556_ = v_isSharedCheck_3582_;
goto v_resetjp_3554_;
}
else
{
lean_inc(v_a_3553_);
lean_inc(v_a_3552_);
lean_dec(v___x_3551_);
v___x_3555_ = lean_box(0);
v_isShared_3556_ = v_isSharedCheck_3582_;
goto v_resetjp_3554_;
}
v_resetjp_3554_:
{
lean_object* v_quotContext_3557_; lean_object* v_currMacroScope_3558_; lean_object* v_ref_3559_; uint8_t v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3580_; 
v_quotContext_3557_ = lean_ctor_get(v_a_3546_, 1);
v_currMacroScope_3558_ = lean_ctor_get(v_a_3546_, 2);
v_ref_3559_ = lean_ctor_get(v_a_3546_, 5);
v___x_3560_ = 0;
v___x_3561_ = l_Lean_SourceInfo_fromRef(v_ref_3559_, v___x_3560_);
v___x_3562_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_3563_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__1, &l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__1_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__1);
v___x_3564_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__2));
lean_inc_n(v_currMacroScope_3558_, 2);
lean_inc_n(v_quotContext_3557_, 2);
v___x_3565_ = l_Lean_addMacroScope(v_quotContext_3557_, v___x_3564_, v_currMacroScope_3558_);
v___x_3566_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__6));
lean_inc_n(v___x_3561_, 3);
v___x_3567_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3567_, 0, v___x_3561_);
lean_ctor_set(v___x_3567_, 1, v___x_3563_);
lean_ctor_set(v___x_3567_, 2, v___x_3565_);
lean_ctor_set(v___x_3567_, 3, v___x_3566_);
v___x_3568_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_3569_ = lean_box(2);
v___x_3570_ = l_Lean_Syntax_mkStrLit(v_name_3549_, v___x_3569_);
v___x_3571_ = l_Lean_Syntax_mkStrLit(v_abbreviation_3550_, v___x_3569_);
v___x_3572_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__8, &l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__8_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__8);
v___x_3573_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__9));
v___x_3574_ = l_Lean_addMacroScope(v_quotContext_3557_, v___x_3573_, v_currMacroScope_3558_);
v___x_3575_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__13));
v___x_3576_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3576_, 0, v___x_3561_);
lean_ctor_set(v___x_3576_, 1, v___x_3572_);
lean_ctor_set(v___x_3576_, 2, v___x_3574_);
lean_ctor_set(v___x_3576_, 3, v___x_3575_);
v___x_3577_ = l_Lean_Syntax_node4(v___x_3561_, v___x_3568_, v_a_3552_, v___x_3570_, v___x_3571_, v___x_3576_);
v___x_3578_ = l_Lean_Syntax_node2(v___x_3561_, v___x_3562_, v___x_3567_, v___x_3577_);
if (v_isShared_3556_ == 0)
{
lean_ctor_set(v___x_3555_, 0, v___x_3578_);
v___x_3580_ = v___x_3555_;
goto v_reusejp_3579_;
}
else
{
lean_object* v_reuseFailAlloc_3581_; 
v_reuseFailAlloc_3581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3581_, 0, v___x_3578_);
lean_ctor_set(v_reuseFailAlloc_3581_, 1, v_a_3553_);
v___x_3580_ = v_reuseFailAlloc_3581_;
goto v_reusejp_3579_;
}
v_reusejp_3579_:
{
return v___x_3580_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertTimezone___boxed(lean_object* v_tz_3583_, lean_object* v_a_3584_, lean_object* v_a_3585_){
_start:
{
lean_object* v_res_3586_; 
v_res_3586_ = l___private_Std_Time_Notation_0__Std_Time_convertTimezone(v_tz_3583_, v_a_3584_, v_a_3585_);
lean_dec_ref(v_a_3584_);
return v_res_3586_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertPlainDate___closed__1(void){
_start:
{
lean_object* v___x_3588_; lean_object* v___x_3589_; 
v___x_3588_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertPlainDate___closed__0));
v___x_3589_ = l_String_toRawSubstring_x27(v___x_3588_);
return v___x_3589_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertPlainDate(lean_object* v_d_3603_, lean_object* v_a_3604_, lean_object* v_a_3605_){
_start:
{
lean_object* v_year_3606_; lean_object* v_month_3607_; lean_object* v_day_3608_; lean_object* v___x_3609_; lean_object* v_a_3610_; lean_object* v_a_3611_; lean_object* v___x_3612_; lean_object* v_a_3613_; lean_object* v_a_3614_; lean_object* v___x_3615_; lean_object* v_a_3616_; lean_object* v_a_3617_; lean_object* v___x_3619_; uint8_t v_isShared_3620_; uint8_t v_isSharedCheck_3638_; 
v_year_3606_ = lean_ctor_get(v_d_3603_, 0);
v_month_3607_ = lean_ctor_get(v_d_3603_, 1);
v_day_3608_ = lean_ctor_get(v_d_3603_, 2);
v___x_3609_ = l___private_Std_Time_Notation_0__Std_Time_syntaxInt(v_year_3606_, v_a_3604_, v_a_3605_);
v_a_3610_ = lean_ctor_get(v___x_3609_, 0);
lean_inc(v_a_3610_);
v_a_3611_ = lean_ctor_get(v___x_3609_, 1);
lean_inc(v_a_3611_);
lean_dec_ref(v___x_3609_);
v___x_3612_ = l___private_Std_Time_Notation_0__Std_Time_syntaxBounded(v_month_3607_, v_a_3604_, v_a_3611_);
v_a_3613_ = lean_ctor_get(v___x_3612_, 0);
lean_inc(v_a_3613_);
v_a_3614_ = lean_ctor_get(v___x_3612_, 1);
lean_inc(v_a_3614_);
lean_dec_ref(v___x_3612_);
v___x_3615_ = l___private_Std_Time_Notation_0__Std_Time_syntaxBounded(v_day_3608_, v_a_3604_, v_a_3614_);
v_a_3616_ = lean_ctor_get(v___x_3615_, 0);
v_a_3617_ = lean_ctor_get(v___x_3615_, 1);
v_isSharedCheck_3638_ = !lean_is_exclusive(v___x_3615_);
if (v_isSharedCheck_3638_ == 0)
{
v___x_3619_ = v___x_3615_;
v_isShared_3620_ = v_isSharedCheck_3638_;
goto v_resetjp_3618_;
}
else
{
lean_inc(v_a_3617_);
lean_inc(v_a_3616_);
lean_dec(v___x_3615_);
v___x_3619_ = lean_box(0);
v_isShared_3620_ = v_isSharedCheck_3638_;
goto v_resetjp_3618_;
}
v_resetjp_3618_:
{
lean_object* v_quotContext_3621_; lean_object* v_currMacroScope_3622_; lean_object* v_ref_3623_; uint8_t v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3636_; 
v_quotContext_3621_ = lean_ctor_get(v_a_3604_, 1);
v_currMacroScope_3622_ = lean_ctor_get(v_a_3604_, 2);
v_ref_3623_ = lean_ctor_get(v_a_3604_, 5);
v___x_3624_ = 0;
v___x_3625_ = l_Lean_SourceInfo_fromRef(v_ref_3623_, v___x_3624_);
v___x_3626_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_3627_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertPlainDate___closed__1, &l___private_Std_Time_Notation_0__Std_Time_convertPlainDate___closed__1_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertPlainDate___closed__1);
v___x_3628_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertPlainDate___closed__4));
lean_inc(v_currMacroScope_3622_);
lean_inc(v_quotContext_3621_);
v___x_3629_ = l_Lean_addMacroScope(v_quotContext_3621_, v___x_3628_, v_currMacroScope_3622_);
v___x_3630_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertPlainDate___closed__6));
lean_inc_n(v___x_3625_, 2);
v___x_3631_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3631_, 0, v___x_3625_);
lean_ctor_set(v___x_3631_, 1, v___x_3627_);
lean_ctor_set(v___x_3631_, 2, v___x_3629_);
lean_ctor_set(v___x_3631_, 3, v___x_3630_);
v___x_3632_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_3633_ = l_Lean_Syntax_node3(v___x_3625_, v___x_3632_, v_a_3610_, v_a_3613_, v_a_3616_);
v___x_3634_ = l_Lean_Syntax_node2(v___x_3625_, v___x_3626_, v___x_3631_, v___x_3633_);
if (v_isShared_3620_ == 0)
{
lean_ctor_set(v___x_3619_, 0, v___x_3634_);
v___x_3636_ = v___x_3619_;
goto v_reusejp_3635_;
}
else
{
lean_object* v_reuseFailAlloc_3637_; 
v_reuseFailAlloc_3637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3637_, 0, v___x_3634_);
lean_ctor_set(v_reuseFailAlloc_3637_, 1, v_a_3617_);
v___x_3636_ = v_reuseFailAlloc_3637_;
goto v_reusejp_3635_;
}
v_reusejp_3635_:
{
return v___x_3636_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertPlainDate___boxed(lean_object* v_d_3639_, lean_object* v_a_3640_, lean_object* v_a_3641_){
_start:
{
lean_object* v_res_3642_; 
v_res_3642_ = l___private_Std_Time_Notation_0__Std_Time_convertPlainDate(v_d_3639_, v_a_3640_, v_a_3641_);
lean_dec_ref(v_a_3640_);
lean_dec_ref(v_d_3639_);
return v_res_3642_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertPlainTime___closed__1(void){
_start:
{
lean_object* v___x_3644_; lean_object* v___x_3645_; 
v___x_3644_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertPlainTime___closed__0));
v___x_3645_ = l_String_toRawSubstring_x27(v___x_3644_);
return v___x_3645_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertPlainTime(lean_object* v_d_3663_, lean_object* v_a_3664_, lean_object* v_a_3665_){
_start:
{
lean_object* v_hour_3666_; lean_object* v_minute_3667_; lean_object* v_second_3668_; lean_object* v_nanosecond_3669_; lean_object* v___x_3671_; uint8_t v_isShared_3672_; uint8_t v_isSharedCheck_3708_; 
v_hour_3666_ = lean_ctor_get(v_d_3663_, 0);
v_minute_3667_ = lean_ctor_get(v_d_3663_, 1);
v_second_3668_ = lean_ctor_get(v_d_3663_, 2);
v_nanosecond_3669_ = lean_ctor_get(v_d_3663_, 3);
v_isSharedCheck_3708_ = !lean_is_exclusive(v_d_3663_);
if (v_isSharedCheck_3708_ == 0)
{
v___x_3671_ = v_d_3663_;
v_isShared_3672_ = v_isSharedCheck_3708_;
goto v_resetjp_3670_;
}
else
{
lean_inc(v_nanosecond_3669_);
lean_inc(v_second_3668_);
lean_inc(v_minute_3667_);
lean_inc(v_hour_3666_);
lean_dec(v_d_3663_);
v___x_3671_ = lean_box(0);
v_isShared_3672_ = v_isSharedCheck_3708_;
goto v_resetjp_3670_;
}
v_resetjp_3670_:
{
lean_object* v___x_3673_; lean_object* v_a_3674_; lean_object* v_a_3675_; lean_object* v___x_3676_; lean_object* v_a_3677_; lean_object* v_a_3678_; lean_object* v___x_3679_; lean_object* v_a_3680_; lean_object* v_a_3681_; lean_object* v___x_3682_; lean_object* v_a_3683_; lean_object* v_a_3684_; lean_object* v___x_3686_; uint8_t v_isShared_3687_; uint8_t v_isSharedCheck_3707_; 
v___x_3673_ = l___private_Std_Time_Notation_0__Std_Time_syntaxBounded(v_hour_3666_, v_a_3664_, v_a_3665_);
lean_dec(v_hour_3666_);
v_a_3674_ = lean_ctor_get(v___x_3673_, 0);
lean_inc(v_a_3674_);
v_a_3675_ = lean_ctor_get(v___x_3673_, 1);
lean_inc(v_a_3675_);
lean_dec_ref(v___x_3673_);
v___x_3676_ = l___private_Std_Time_Notation_0__Std_Time_syntaxBounded(v_minute_3667_, v_a_3664_, v_a_3675_);
lean_dec(v_minute_3667_);
v_a_3677_ = lean_ctor_get(v___x_3676_, 0);
lean_inc(v_a_3677_);
v_a_3678_ = lean_ctor_get(v___x_3676_, 1);
lean_inc(v_a_3678_);
lean_dec_ref(v___x_3676_);
v___x_3679_ = l___private_Std_Time_Notation_0__Std_Time_syntaxBounded(v_second_3668_, v_a_3664_, v_a_3678_);
lean_dec(v_second_3668_);
v_a_3680_ = lean_ctor_get(v___x_3679_, 0);
lean_inc(v_a_3680_);
v_a_3681_ = lean_ctor_get(v___x_3679_, 1);
lean_inc(v_a_3681_);
lean_dec_ref(v___x_3679_);
v___x_3682_ = l___private_Std_Time_Notation_0__Std_Time_syntaxBounded(v_nanosecond_3669_, v_a_3664_, v_a_3681_);
lean_dec(v_nanosecond_3669_);
v_a_3683_ = lean_ctor_get(v___x_3682_, 0);
v_a_3684_ = lean_ctor_get(v___x_3682_, 1);
v_isSharedCheck_3707_ = !lean_is_exclusive(v___x_3682_);
if (v_isSharedCheck_3707_ == 0)
{
v___x_3686_ = v___x_3682_;
v_isShared_3687_ = v_isSharedCheck_3707_;
goto v_resetjp_3685_;
}
else
{
lean_inc(v_a_3684_);
lean_inc(v_a_3683_);
lean_dec(v___x_3682_);
v___x_3686_ = lean_box(0);
v_isShared_3687_ = v_isSharedCheck_3707_;
goto v_resetjp_3685_;
}
v_resetjp_3685_:
{
lean_object* v_quotContext_3688_; lean_object* v_currMacroScope_3689_; lean_object* v_ref_3690_; uint8_t v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3699_; 
v_quotContext_3688_ = lean_ctor_get(v_a_3664_, 1);
v_currMacroScope_3689_ = lean_ctor_get(v_a_3664_, 2);
v_ref_3690_ = lean_ctor_get(v_a_3664_, 5);
v___x_3691_ = 0;
v___x_3692_ = l_Lean_SourceInfo_fromRef(v_ref_3690_, v___x_3691_);
v___x_3693_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_3694_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertPlainTime___closed__1, &l___private_Std_Time_Notation_0__Std_Time_convertPlainTime___closed__1_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertPlainTime___closed__1);
v___x_3695_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertPlainTime___closed__3));
lean_inc(v_currMacroScope_3689_);
lean_inc(v_quotContext_3688_);
v___x_3696_ = l_Lean_addMacroScope(v_quotContext_3688_, v___x_3695_, v_currMacroScope_3689_);
v___x_3697_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertPlainTime___closed__7));
lean_inc(v___x_3692_);
if (v_isShared_3672_ == 0)
{
lean_ctor_set_tag(v___x_3671_, 3);
lean_ctor_set(v___x_3671_, 3, v___x_3697_);
lean_ctor_set(v___x_3671_, 2, v___x_3696_);
lean_ctor_set(v___x_3671_, 1, v___x_3694_);
lean_ctor_set(v___x_3671_, 0, v___x_3692_);
v___x_3699_ = v___x_3671_;
goto v_reusejp_3698_;
}
else
{
lean_object* v_reuseFailAlloc_3706_; 
v_reuseFailAlloc_3706_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3706_, 0, v___x_3692_);
lean_ctor_set(v_reuseFailAlloc_3706_, 1, v___x_3694_);
lean_ctor_set(v_reuseFailAlloc_3706_, 2, v___x_3696_);
lean_ctor_set(v_reuseFailAlloc_3706_, 3, v___x_3697_);
v___x_3699_ = v_reuseFailAlloc_3706_;
goto v_reusejp_3698_;
}
v_reusejp_3698_:
{
lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3704_; 
v___x_3700_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
lean_inc(v___x_3692_);
v___x_3701_ = l_Lean_Syntax_node4(v___x_3692_, v___x_3700_, v_a_3674_, v_a_3677_, v_a_3680_, v_a_3683_);
v___x_3702_ = l_Lean_Syntax_node2(v___x_3692_, v___x_3693_, v___x_3699_, v___x_3701_);
if (v_isShared_3687_ == 0)
{
lean_ctor_set(v___x_3686_, 0, v___x_3702_);
v___x_3704_ = v___x_3686_;
goto v_reusejp_3703_;
}
else
{
lean_object* v_reuseFailAlloc_3705_; 
v_reuseFailAlloc_3705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3705_, 0, v___x_3702_);
lean_ctor_set(v_reuseFailAlloc_3705_, 1, v_a_3684_);
v___x_3704_ = v_reuseFailAlloc_3705_;
goto v_reusejp_3703_;
}
v_reusejp_3703_:
{
return v___x_3704_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertPlainTime___boxed(lean_object* v_d_3709_, lean_object* v_a_3710_, lean_object* v_a_3711_){
_start:
{
lean_object* v_res_3712_; 
v_res_3712_ = l___private_Std_Time_Notation_0__Std_Time_convertPlainTime(v_d_3709_, v_a_3710_, v_a_3711_);
lean_dec_ref(v_a_3710_);
return v_res_3712_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime___closed__1(void){
_start:
{
lean_object* v___x_3714_; lean_object* v___x_3715_; 
v___x_3714_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime___closed__0));
v___x_3715_ = l_String_toRawSubstring_x27(v___x_3714_);
return v___x_3715_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime(lean_object* v_d_3733_, lean_object* v_a_3734_, lean_object* v_a_3735_){
_start:
{
lean_object* v_date_3736_; lean_object* v_time_3737_; lean_object* v___x_3738_; lean_object* v_a_3739_; lean_object* v_a_3740_; lean_object* v___x_3741_; lean_object* v_a_3742_; lean_object* v_a_3743_; lean_object* v___x_3745_; uint8_t v_isShared_3746_; uint8_t v_isSharedCheck_3764_; 
v_date_3736_ = lean_ctor_get(v_d_3733_, 0);
lean_inc_ref(v_date_3736_);
v_time_3737_ = lean_ctor_get(v_d_3733_, 1);
lean_inc_ref(v_time_3737_);
lean_dec_ref(v_d_3733_);
v___x_3738_ = l___private_Std_Time_Notation_0__Std_Time_convertPlainDate(v_date_3736_, v_a_3734_, v_a_3735_);
lean_dec_ref(v_date_3736_);
v_a_3739_ = lean_ctor_get(v___x_3738_, 0);
lean_inc(v_a_3739_);
v_a_3740_ = lean_ctor_get(v___x_3738_, 1);
lean_inc(v_a_3740_);
lean_dec_ref(v___x_3738_);
v___x_3741_ = l___private_Std_Time_Notation_0__Std_Time_convertPlainTime(v_time_3737_, v_a_3734_, v_a_3740_);
v_a_3742_ = lean_ctor_get(v___x_3741_, 0);
v_a_3743_ = lean_ctor_get(v___x_3741_, 1);
v_isSharedCheck_3764_ = !lean_is_exclusive(v___x_3741_);
if (v_isSharedCheck_3764_ == 0)
{
v___x_3745_ = v___x_3741_;
v_isShared_3746_ = v_isSharedCheck_3764_;
goto v_resetjp_3744_;
}
else
{
lean_inc(v_a_3743_);
lean_inc(v_a_3742_);
lean_dec(v___x_3741_);
v___x_3745_ = lean_box(0);
v_isShared_3746_ = v_isSharedCheck_3764_;
goto v_resetjp_3744_;
}
v_resetjp_3744_:
{
lean_object* v_quotContext_3747_; lean_object* v_currMacroScope_3748_; lean_object* v_ref_3749_; uint8_t v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3762_; 
v_quotContext_3747_ = lean_ctor_get(v_a_3734_, 1);
v_currMacroScope_3748_ = lean_ctor_get(v_a_3734_, 2);
v_ref_3749_ = lean_ctor_get(v_a_3734_, 5);
v___x_3750_ = 0;
v___x_3751_ = l_Lean_SourceInfo_fromRef(v_ref_3749_, v___x_3750_);
v___x_3752_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_3753_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime___closed__1, &l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime___closed__1_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime___closed__1);
v___x_3754_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime___closed__3));
lean_inc(v_currMacroScope_3748_);
lean_inc(v_quotContext_3747_);
v___x_3755_ = l_Lean_addMacroScope(v_quotContext_3747_, v___x_3754_, v_currMacroScope_3748_);
v___x_3756_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime___closed__7));
lean_inc_n(v___x_3751_, 2);
v___x_3757_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3757_, 0, v___x_3751_);
lean_ctor_set(v___x_3757_, 1, v___x_3753_);
lean_ctor_set(v___x_3757_, 2, v___x_3755_);
lean_ctor_set(v___x_3757_, 3, v___x_3756_);
v___x_3758_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_3759_ = l_Lean_Syntax_node2(v___x_3751_, v___x_3758_, v_a_3739_, v_a_3742_);
v___x_3760_ = l_Lean_Syntax_node2(v___x_3751_, v___x_3752_, v___x_3757_, v___x_3759_);
if (v_isShared_3746_ == 0)
{
lean_ctor_set(v___x_3745_, 0, v___x_3760_);
v___x_3762_ = v___x_3745_;
goto v_reusejp_3761_;
}
else
{
lean_object* v_reuseFailAlloc_3763_; 
v_reuseFailAlloc_3763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3763_, 0, v___x_3760_);
lean_ctor_set(v_reuseFailAlloc_3763_, 1, v_a_3743_);
v___x_3762_ = v_reuseFailAlloc_3763_;
goto v_reusejp_3761_;
}
v_reusejp_3761_:
{
return v___x_3762_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime___boxed(lean_object* v_d_3765_, lean_object* v_a_3766_, lean_object* v_a_3767_){
_start:
{
lean_object* v_res_3768_; 
v_res_3768_ = l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime(v_d_3765_, v_a_3766_, v_a_3767_);
lean_dec_ref(v_a_3766_);
return v_res_3768_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__1(void){
_start:
{
lean_object* v___x_3770_; lean_object* v___x_3771_; 
v___x_3770_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__0));
v___x_3771_ = l_String_toRawSubstring_x27(v___x_3770_);
return v___x_3771_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__8(void){
_start:
{
lean_object* v___x_3786_; lean_object* v___x_3787_; 
v___x_3786_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__7));
v___x_3787_ = l_String_toRawSubstring_x27(v___x_3786_);
return v___x_3787_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__21(void){
_start:
{
lean_object* v___x_3814_; lean_object* v___x_3815_; 
v___x_3814_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__20));
v___x_3815_ = l_String_toRawSubstring_x27(v___x_3814_);
return v___x_3815_;
}
}
lean_object* l___private_Std_Time_Notation_0__Std_Time_convertDateTime(lean_object* v_d_3822_, uint8_t v_identifier_3823_, lean_object* v_a_3824_, lean_object* v_a_3825_){
_start:
{
lean_object* v_date_3826_; lean_object* v_timezone_3827_; lean_object* v___x_3829_; uint8_t v_isShared_3830_; uint8_t v_isSharedCheck_3921_; 
v_date_3826_ = lean_ctor_get(v_d_3822_, 0);
v_timezone_3827_ = lean_ctor_get(v_d_3822_, 3);
v_isSharedCheck_3921_ = !lean_is_exclusive(v_d_3822_);
if (v_isSharedCheck_3921_ == 0)
{
lean_object* v_unused_3922_; lean_object* v_unused_3923_; 
v_unused_3922_ = lean_ctor_get(v_d_3822_, 2);
lean_dec(v_unused_3922_);
v_unused_3923_ = lean_ctor_get(v_d_3822_, 1);
lean_dec(v_unused_3923_);
v___x_3829_ = v_d_3822_;
v_isShared_3830_ = v_isSharedCheck_3921_;
goto v_resetjp_3828_;
}
else
{
lean_inc(v_timezone_3827_);
lean_inc(v_date_3826_);
lean_dec(v_d_3822_);
v___x_3829_ = lean_box(0);
v_isShared_3830_ = v_isSharedCheck_3921_;
goto v_resetjp_3828_;
}
v_resetjp_3828_:
{
lean_object* v___x_3831_; lean_object* v___x_3832_; 
v___x_3831_ = lean_thunk_get_own(v_date_3826_);
lean_dec_ref(v_date_3826_);
v___x_3832_ = l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime(v___x_3831_, v_a_3824_, v_a_3825_);
if (v_identifier_3823_ == 0)
{
lean_object* v_a_3833_; lean_object* v_a_3834_; lean_object* v___x_3835_; lean_object* v_a_3836_; lean_object* v_a_3837_; lean_object* v___x_3839_; uint8_t v_isShared_3840_; uint8_t v_isSharedCheck_3881_; 
v_a_3833_ = lean_ctor_get(v___x_3832_, 0);
lean_inc(v_a_3833_);
v_a_3834_ = lean_ctor_get(v___x_3832_, 1);
lean_inc(v_a_3834_);
lean_dec_ref(v___x_3832_);
v___x_3835_ = l___private_Std_Time_Notation_0__Std_Time_convertTimezone(v_timezone_3827_, v_a_3824_, v_a_3834_);
v_a_3836_ = lean_ctor_get(v___x_3835_, 0);
v_a_3837_ = lean_ctor_get(v___x_3835_, 1);
v_isSharedCheck_3881_ = !lean_is_exclusive(v___x_3835_);
if (v_isSharedCheck_3881_ == 0)
{
v___x_3839_ = v___x_3835_;
v_isShared_3840_ = v_isSharedCheck_3881_;
goto v_resetjp_3838_;
}
else
{
lean_inc(v_a_3837_);
lean_inc(v_a_3836_);
lean_dec(v___x_3835_);
v___x_3839_ = lean_box(0);
v_isShared_3840_ = v_isSharedCheck_3881_;
goto v_resetjp_3838_;
}
v_resetjp_3838_:
{
lean_object* v_quotContext_3841_; lean_object* v_currMacroScope_3842_; lean_object* v_ref_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3851_; 
v_quotContext_3841_ = lean_ctor_get(v_a_3824_, 1);
v_currMacroScope_3842_ = lean_ctor_get(v_a_3824_, 2);
v_ref_3843_ = lean_ctor_get(v_a_3824_, 5);
v___x_3844_ = l_Lean_SourceInfo_fromRef(v_ref_3843_, v_identifier_3823_);
v___x_3845_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_3846_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__1, &l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__1_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__1);
v___x_3847_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__4));
lean_inc(v_currMacroScope_3842_);
lean_inc(v_quotContext_3841_);
v___x_3848_ = l_Lean_addMacroScope(v_quotContext_3841_, v___x_3847_, v_currMacroScope_3842_);
v___x_3849_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__6));
lean_inc(v___x_3844_);
if (v_isShared_3830_ == 0)
{
lean_ctor_set_tag(v___x_3829_, 3);
lean_ctor_set(v___x_3829_, 3, v___x_3849_);
lean_ctor_set(v___x_3829_, 2, v___x_3848_);
lean_ctor_set(v___x_3829_, 1, v___x_3846_);
lean_ctor_set(v___x_3829_, 0, v___x_3844_);
v___x_3851_ = v___x_3829_;
goto v_reusejp_3850_;
}
else
{
lean_object* v_reuseFailAlloc_3880_; 
v_reuseFailAlloc_3880_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3880_, 0, v___x_3844_);
lean_ctor_set(v_reuseFailAlloc_3880_, 1, v___x_3846_);
lean_ctor_set(v_reuseFailAlloc_3880_, 2, v___x_3848_);
lean_ctor_set(v_reuseFailAlloc_3880_, 3, v___x_3849_);
v___x_3851_ = v_reuseFailAlloc_3880_;
goto v_reusejp_3850_;
}
v_reusejp_3850_:
{
lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3878_; 
v___x_3852_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_3853_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__42));
v___x_3854_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__44));
v___x_3855_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__45));
lean_inc_n(v___x_3844_, 10);
v___x_3856_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3856_, 0, v___x_3844_);
lean_ctor_set(v___x_3856_, 1, v___x_3855_);
v___x_3857_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__47));
v___x_3858_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49);
v___x_3859_ = lean_box(0);
lean_inc_n(v_currMacroScope_3842_, 2);
lean_inc_n(v_quotContext_3841_, 2);
v___x_3860_ = l_Lean_addMacroScope(v_quotContext_3841_, v___x_3859_, v_currMacroScope_3842_);
v___x_3861_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__65));
v___x_3862_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3862_, 0, v___x_3844_);
lean_ctor_set(v___x_3862_, 1, v___x_3858_);
lean_ctor_set(v___x_3862_, 2, v___x_3860_);
lean_ctor_set(v___x_3862_, 3, v___x_3861_);
v___x_3863_ = l_Lean_Syntax_node1(v___x_3844_, v___x_3857_, v___x_3862_);
v___x_3864_ = l_Lean_Syntax_node2(v___x_3844_, v___x_3854_, v___x_3856_, v___x_3863_);
v___x_3865_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__8, &l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__8_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__8);
v___x_3866_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__11));
v___x_3867_ = l_Lean_addMacroScope(v_quotContext_3841_, v___x_3866_, v_currMacroScope_3842_);
v___x_3868_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__13));
v___x_3869_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3869_, 0, v___x_3844_);
lean_ctor_set(v___x_3869_, 1, v___x_3865_);
lean_ctor_set(v___x_3869_, 2, v___x_3867_);
lean_ctor_set(v___x_3869_, 3, v___x_3868_);
v___x_3870_ = l_Lean_Syntax_node1(v___x_3844_, v___x_3852_, v_a_3836_);
v___x_3871_ = l_Lean_Syntax_node2(v___x_3844_, v___x_3845_, v___x_3869_, v___x_3870_);
v___x_3872_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__72));
v___x_3873_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3873_, 0, v___x_3844_);
lean_ctor_set(v___x_3873_, 1, v___x_3872_);
v___x_3874_ = l_Lean_Syntax_node3(v___x_3844_, v___x_3853_, v___x_3864_, v___x_3871_, v___x_3873_);
v___x_3875_ = l_Lean_Syntax_node2(v___x_3844_, v___x_3852_, v_a_3833_, v___x_3874_);
v___x_3876_ = l_Lean_Syntax_node2(v___x_3844_, v___x_3845_, v___x_3851_, v___x_3875_);
if (v_isShared_3840_ == 0)
{
lean_ctor_set(v___x_3839_, 0, v___x_3876_);
v___x_3878_ = v___x_3839_;
goto v_reusejp_3877_;
}
else
{
lean_object* v_reuseFailAlloc_3879_; 
v_reuseFailAlloc_3879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3879_, 0, v___x_3876_);
lean_ctor_set(v_reuseFailAlloc_3879_, 1, v_a_3837_);
v___x_3878_ = v_reuseFailAlloc_3879_;
goto v_reusejp_3877_;
}
v_reusejp_3877_:
{
return v___x_3878_;
}
}
}
}
else
{
lean_object* v_a_3882_; lean_object* v_a_3883_; lean_object* v___x_3885_; uint8_t v_isShared_3886_; uint8_t v_isSharedCheck_3920_; 
v_a_3882_ = lean_ctor_get(v___x_3832_, 0);
v_a_3883_ = lean_ctor_get(v___x_3832_, 1);
v_isSharedCheck_3920_ = !lean_is_exclusive(v___x_3832_);
if (v_isSharedCheck_3920_ == 0)
{
v___x_3885_ = v___x_3832_;
v_isShared_3886_ = v_isSharedCheck_3920_;
goto v_resetjp_3884_;
}
else
{
lean_inc(v_a_3883_);
lean_inc(v_a_3882_);
lean_dec(v___x_3832_);
v___x_3885_ = lean_box(0);
v_isShared_3886_ = v_isSharedCheck_3920_;
goto v_resetjp_3884_;
}
v_resetjp_3884_:
{
lean_object* v_quotContext_3887_; lean_object* v_currMacroScope_3888_; lean_object* v_ref_3889_; uint8_t v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3898_; 
v_quotContext_3887_ = lean_ctor_get(v_a_3824_, 1);
v_currMacroScope_3888_ = lean_ctor_get(v_a_3824_, 2);
v_ref_3889_ = lean_ctor_get(v_a_3824_, 5);
v___x_3890_ = 0;
v___x_3891_ = l_Lean_SourceInfo_fromRef(v_ref_3889_, v___x_3890_);
v___x_3892_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_3893_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__1, &l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__1_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__1);
v___x_3894_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__4));
lean_inc(v_currMacroScope_3888_);
lean_inc(v_quotContext_3887_);
v___x_3895_ = l_Lean_addMacroScope(v_quotContext_3887_, v___x_3894_, v_currMacroScope_3888_);
v___x_3896_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__6));
lean_inc(v___x_3891_);
if (v_isShared_3830_ == 0)
{
lean_ctor_set_tag(v___x_3829_, 3);
lean_ctor_set(v___x_3829_, 3, v___x_3896_);
lean_ctor_set(v___x_3829_, 2, v___x_3895_);
lean_ctor_set(v___x_3829_, 1, v___x_3893_);
lean_ctor_set(v___x_3829_, 0, v___x_3891_);
v___x_3898_ = v___x_3829_;
goto v_reusejp_3897_;
}
else
{
lean_object* v_reuseFailAlloc_3919_; 
v_reuseFailAlloc_3919_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3919_, 0, v___x_3891_);
lean_ctor_set(v_reuseFailAlloc_3919_, 1, v___x_3893_);
lean_ctor_set(v_reuseFailAlloc_3919_, 2, v___x_3895_);
lean_ctor_set(v_reuseFailAlloc_3919_, 3, v___x_3896_);
v___x_3898_ = v_reuseFailAlloc_3919_;
goto v_reusejp_3897_;
}
v_reusejp_3897_:
{
lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v_name_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3917_; 
v___x_3899_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
lean_inc_n(v___x_3891_, 6);
v___x_3900_ = l_Lean_Syntax_node1(v___x_3891_, v___x_3899_, v_a_3882_);
v___x_3901_ = l_Lean_Syntax_node2(v___x_3891_, v___x_3892_, v___x_3898_, v___x_3900_);
v_name_3902_ = lean_ctor_get(v_timezone_3827_, 1);
lean_inc_ref(v_name_3902_);
lean_dec_ref(v_timezone_3827_);
v___x_3903_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__14));
v___x_3904_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3904_, 0, v___x_3891_);
lean_ctor_set(v___x_3904_, 1, v___x_3903_);
v___x_3905_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__17));
lean_inc(v_currMacroScope_3888_);
lean_inc(v_quotContext_3887_);
v___x_3906_ = l_Lean_addMacroScope(v_quotContext_3887_, v___x_3905_, v_currMacroScope_3888_);
v___x_3907_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__19));
v___x_3908_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__21, &l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__21_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__21);
v___x_3909_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__23));
v___x_3910_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3910_, 0, v___x_3891_);
lean_ctor_set(v___x_3910_, 1, v___x_3908_);
lean_ctor_set(v___x_3910_, 2, v___x_3906_);
lean_ctor_set(v___x_3910_, 3, v___x_3909_);
v___x_3911_ = lean_box(2);
v___x_3912_ = l_Lean_Syntax_mkStrLit(v_name_3902_, v___x_3911_);
v___x_3913_ = l_Lean_Syntax_node1(v___x_3891_, v___x_3899_, v___x_3912_);
v___x_3914_ = l_Lean_Syntax_node2(v___x_3891_, v___x_3892_, v___x_3910_, v___x_3913_);
v___x_3915_ = l_Lean_Syntax_node3(v___x_3891_, v___x_3907_, v___x_3901_, v___x_3904_, v___x_3914_);
if (v_isShared_3886_ == 0)
{
lean_ctor_set(v___x_3885_, 0, v___x_3915_);
v___x_3917_ = v___x_3885_;
goto v_reusejp_3916_;
}
else
{
lean_object* v_reuseFailAlloc_3918_; 
v_reuseFailAlloc_3918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3918_, 0, v___x_3915_);
lean_ctor_set(v_reuseFailAlloc_3918_, 1, v_a_3883_);
v___x_3917_ = v_reuseFailAlloc_3918_;
goto v_reusejp_3916_;
}
v_reusejp_3916_:
{
return v___x_3917_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Time_Notation_0__Std_Time_convertDateTime_0interp(lean_interpreter_value* stack)
{
lean_object* v_d_3822_ = stack[0].m_obj;
uint8_t v_identifier_3823_ = stack[1].m_num;
lean_object* v_a_3824_ = stack[2].m_obj;
lean_object* v_a_3825_ = stack[3].m_obj;
lean_object* v_res_3924_;
v_res_3924_ = l___private_Std_Time_Notation_0__Std_Time_convertDateTime(v_d_3822_, v_identifier_3823_, v_a_3824_, v_a_3825_);
stack->m_obj
 = v_res_3924_;
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertDateTime___boxed(lean_object* v_d_3925_, lean_object* v_identifier_3926_, lean_object* v_a_3927_, lean_object* v_a_3928_){
_start:
{
uint8_t v_identifier_boxed_3929_; lean_object* v_res_3930_; 
v_identifier_boxed_3929_ = lean_unbox(v_identifier_3926_);
v_res_3930_ = l___private_Std_Time_Notation_0__Std_Time_convertDateTime(v_d_3925_, v_identifier_boxed_3929_, v_a_3927_, v_a_3928_);
lean_dec_ref(v_a_3927_);
return v_res_3930_;
}
}
LEAN_EXPORT lean_object* l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termZoned_x28___x29__1(lean_object* v_x_4096_, lean_object* v_a_4097_, lean_object* v_a_4098_){
_start:
{
lean_object* v___x_4099_; uint8_t v___x_4100_; 
v___x_4099_ = ((lean_object*)(l_Std_Time_termZoned_x28___x29___closed__1));
lean_inc(v_x_4096_);
v___x_4100_ = l_Lean_Syntax_isOfKind(v_x_4096_, v___x_4099_);
if (v___x_4100_ == 0)
{
lean_object* v___x_4101_; lean_object* v___x_4102_; 
lean_dec(v_x_4096_);
v___x_4101_ = lean_box(1);
v___x_4102_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4102_, 0, v___x_4101_);
lean_ctor_set(v___x_4102_, 1, v_a_4098_);
return v___x_4102_;
}
else
{
lean_object* v___x_4103_; lean_object* v_date_4104_; lean_object* v___x_4105_; uint8_t v___x_4106_; 
v___x_4103_ = lean_unsigned_to_nat(1u);
v_date_4104_ = l_Lean_Syntax_getArg(v_x_4096_, v___x_4103_);
lean_dec(v_x_4096_);
v___x_4105_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxString___closed__1));
lean_inc(v_date_4104_);
v___x_4106_ = l_Lean_Syntax_isOfKind(v_date_4104_, v___x_4105_);
if (v___x_4106_ == 0)
{
lean_object* v___x_4107_; lean_object* v___x_4108_; 
lean_dec(v_date_4104_);
v___x_4107_ = lean_box(1);
v___x_4108_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4108_, 0, v___x_4107_);
lean_ctor_set(v___x_4108_, 1, v_a_4098_);
return v___x_4108_;
}
else
{
lean_object* v___x_4109_; lean_object* v___x_4110_; 
v___x_4109_ = l_Lean_TSyntax_getString(v_date_4104_);
lean_inc_ref(v___x_4109_);
v___x_4110_ = l_Std_Time_DateTime_fromLeanDateTimeWithZoneString(v___x_4109_);
if (lean_obj_tag(v___x_4110_) == 0)
{
lean_object* v___x_4111_; 
lean_dec_ref_known(v___x_4110_, 1);
v___x_4111_ = l_Std_Time_DateTime_fromLeanDateTimeWithIdentifierString(v___x_4109_);
if (lean_obj_tag(v___x_4111_) == 0)
{
lean_object* v_a_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; 
v_a_4112_ = lean_ctor_get(v___x_4111_, 0);
lean_inc(v_a_4112_);
lean_dec_ref_known(v___x_4111_, 1);
v___x_4113_ = ((lean_object*)(l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termZoned_x28___x29__1___closed__0));
v___x_4114_ = lean_string_append(v___x_4113_, v_a_4112_);
lean_dec(v_a_4112_);
v___x_4115_ = l_Lean_Macro_throwErrorAt___redArg(v_date_4104_, v___x_4114_, v_a_4097_, v_a_4098_);
lean_dec(v_date_4104_);
return v___x_4115_;
}
else
{
lean_object* v_a_4116_; lean_object* v___x_4117_; lean_object* v_a_4118_; lean_object* v_a_4119_; lean_object* v___x_4121_; uint8_t v_isShared_4122_; uint8_t v_isSharedCheck_4126_; 
lean_dec(v_date_4104_);
v_a_4116_ = lean_ctor_get(v___x_4111_, 0);
lean_inc(v_a_4116_);
lean_dec_ref_known(v___x_4111_, 1);
v___x_4117_ = l___private_Std_Time_Notation_0__Std_Time_convertDateTime(v_a_4116_, v___x_4106_, v_a_4097_, v_a_4098_);
v_a_4118_ = lean_ctor_get(v___x_4117_, 0);
v_a_4119_ = lean_ctor_get(v___x_4117_, 1);
v_isSharedCheck_4126_ = !lean_is_exclusive(v___x_4117_);
if (v_isSharedCheck_4126_ == 0)
{
v___x_4121_ = v___x_4117_;
v_isShared_4122_ = v_isSharedCheck_4126_;
goto v_resetjp_4120_;
}
else
{
lean_inc(v_a_4119_);
lean_inc(v_a_4118_);
lean_dec(v___x_4117_);
v___x_4121_ = lean_box(0);
v_isShared_4122_ = v_isSharedCheck_4126_;
goto v_resetjp_4120_;
}
v_resetjp_4120_:
{
lean_object* v___x_4124_; 
if (v_isShared_4122_ == 0)
{
v___x_4124_ = v___x_4121_;
goto v_reusejp_4123_;
}
else
{
lean_object* v_reuseFailAlloc_4125_; 
v_reuseFailAlloc_4125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4125_, 0, v_a_4118_);
lean_ctor_set(v_reuseFailAlloc_4125_, 1, v_a_4119_);
v___x_4124_ = v_reuseFailAlloc_4125_;
goto v_reusejp_4123_;
}
v_reusejp_4123_:
{
return v___x_4124_;
}
}
}
}
else
{
lean_object* v_a_4127_; uint8_t v___x_4128_; lean_object* v___x_4129_; lean_object* v_a_4130_; lean_object* v_a_4131_; lean_object* v___x_4133_; uint8_t v_isShared_4134_; uint8_t v_isSharedCheck_4138_; 
lean_dec_ref(v___x_4109_);
lean_dec(v_date_4104_);
v_a_4127_ = lean_ctor_get(v___x_4110_, 0);
lean_inc(v_a_4127_);
lean_dec_ref_known(v___x_4110_, 1);
v___x_4128_ = 0;
v___x_4129_ = l___private_Std_Time_Notation_0__Std_Time_convertDateTime(v_a_4127_, v___x_4128_, v_a_4097_, v_a_4098_);
v_a_4130_ = lean_ctor_get(v___x_4129_, 0);
v_a_4131_ = lean_ctor_get(v___x_4129_, 1);
v_isSharedCheck_4138_ = !lean_is_exclusive(v___x_4129_);
if (v_isSharedCheck_4138_ == 0)
{
v___x_4133_ = v___x_4129_;
v_isShared_4134_ = v_isSharedCheck_4138_;
goto v_resetjp_4132_;
}
else
{
lean_inc(v_a_4131_);
lean_inc(v_a_4130_);
lean_dec(v___x_4129_);
v___x_4133_ = lean_box(0);
v_isShared_4134_ = v_isSharedCheck_4138_;
goto v_resetjp_4132_;
}
v_resetjp_4132_:
{
lean_object* v___x_4136_; 
if (v_isShared_4134_ == 0)
{
v___x_4136_ = v___x_4133_;
goto v_reusejp_4135_;
}
else
{
lean_object* v_reuseFailAlloc_4137_; 
v_reuseFailAlloc_4137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4137_, 0, v_a_4130_);
lean_ctor_set(v_reuseFailAlloc_4137_, 1, v_a_4131_);
v___x_4136_ = v_reuseFailAlloc_4137_;
goto v_reusejp_4135_;
}
v_reusejp_4135_:
{
return v___x_4136_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termZoned_x28___x29__1___boxed(lean_object* v_x_4139_, lean_object* v_a_4140_, lean_object* v_a_4141_){
_start:
{
lean_object* v_res_4142_; 
v_res_4142_ = l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termZoned_x28___x29__1(v_x_4139_, v_a_4140_, v_a_4141_);
lean_dec_ref(v_a_4140_);
return v_res_4142_;
}
}
LEAN_EXPORT lean_object* l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termZoned_x28___x2c___x29__1(lean_object* v_x_4143_, lean_object* v_a_4144_, lean_object* v_a_4145_){
_start:
{
lean_object* v___x_4146_; uint8_t v___x_4147_; 
v___x_4146_ = ((lean_object*)(l_Std_Time_termZoned_x28___x2c___x29___closed__1));
lean_inc(v_x_4143_);
v___x_4147_ = l_Lean_Syntax_isOfKind(v_x_4143_, v___x_4146_);
if (v___x_4147_ == 0)
{
lean_object* v___x_4148_; lean_object* v___x_4149_; 
lean_dec(v_x_4143_);
v___x_4148_ = lean_box(1);
v___x_4149_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4149_, 0, v___x_4148_);
lean_ctor_set(v___x_4149_, 1, v_a_4145_);
return v___x_4149_;
}
else
{
lean_object* v___x_4150_; lean_object* v_date_4151_; lean_object* v___x_4152_; uint8_t v___x_4153_; 
v___x_4150_ = lean_unsigned_to_nat(1u);
v_date_4151_ = l_Lean_Syntax_getArg(v_x_4143_, v___x_4150_);
v___x_4152_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxString___closed__1));
lean_inc(v_date_4151_);
v___x_4153_ = l_Lean_Syntax_isOfKind(v_date_4151_, v___x_4152_);
if (v___x_4153_ == 0)
{
lean_object* v___x_4154_; lean_object* v___x_4155_; 
lean_dec(v_date_4151_);
lean_dec(v_x_4143_);
v___x_4154_ = lean_box(1);
v___x_4155_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4155_, 0, v___x_4154_);
lean_ctor_set(v___x_4155_, 1, v_a_4145_);
return v___x_4155_;
}
else
{
lean_object* v___x_4156_; lean_object* v___x_4157_; 
v___x_4156_ = l_Lean_TSyntax_getString(v_date_4151_);
v___x_4157_ = l_Std_Time_PlainDateTime_fromLeanDateTimeString(v___x_4156_);
if (lean_obj_tag(v___x_4157_) == 0)
{
lean_object* v_a_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; 
lean_dec(v_x_4143_);
v_a_4158_ = lean_ctor_get(v___x_4157_, 0);
lean_inc(v_a_4158_);
lean_dec_ref_known(v___x_4157_, 1);
v___x_4159_ = ((lean_object*)(l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termZoned_x28___x29__1___closed__0));
v___x_4160_ = lean_string_append(v___x_4159_, v_a_4158_);
lean_dec(v_a_4158_);
v___x_4161_ = l_Lean_Macro_throwErrorAt___redArg(v_date_4151_, v___x_4160_, v_a_4144_, v_a_4145_);
lean_dec(v_date_4151_);
return v___x_4161_;
}
else
{
lean_object* v_a_4162_; lean_object* v___x_4163_; lean_object* v_a_4164_; lean_object* v_a_4165_; lean_object* v___x_4167_; uint8_t v_isShared_4168_; uint8_t v_isSharedCheck_4188_; 
lean_dec(v_date_4151_);
v_a_4162_ = lean_ctor_get(v___x_4157_, 0);
lean_inc(v_a_4162_);
lean_dec_ref_known(v___x_4157_, 1);
v___x_4163_ = l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime(v_a_4162_, v_a_4144_, v_a_4145_);
v_a_4164_ = lean_ctor_get(v___x_4163_, 0);
v_a_4165_ = lean_ctor_get(v___x_4163_, 1);
v_isSharedCheck_4188_ = !lean_is_exclusive(v___x_4163_);
if (v_isSharedCheck_4188_ == 0)
{
v___x_4167_ = v___x_4163_;
v_isShared_4168_ = v_isSharedCheck_4188_;
goto v_resetjp_4166_;
}
else
{
lean_inc(v_a_4165_);
lean_inc(v_a_4164_);
lean_dec(v___x_4163_);
v___x_4167_ = lean_box(0);
v_isShared_4168_ = v_isSharedCheck_4188_;
goto v_resetjp_4166_;
}
v_resetjp_4166_:
{
lean_object* v_quotContext_4169_; lean_object* v_currMacroScope_4170_; lean_object* v_ref_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; uint8_t v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4186_; 
v_quotContext_4169_ = lean_ctor_get(v_a_4144_, 1);
v_currMacroScope_4170_ = lean_ctor_get(v_a_4144_, 2);
v_ref_4171_ = lean_ctor_get(v_a_4144_, 5);
v___x_4172_ = lean_unsigned_to_nat(3u);
v___x_4173_ = l_Lean_Syntax_getArg(v_x_4143_, v___x_4172_);
lean_dec(v_x_4143_);
v___x_4174_ = 0;
v___x_4175_ = l_Lean_SourceInfo_fromRef(v_ref_4171_, v___x_4174_);
v___x_4176_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_4177_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__1, &l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__1_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__1);
v___x_4178_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__4));
lean_inc(v_currMacroScope_4170_);
lean_inc(v_quotContext_4169_);
v___x_4179_ = l_Lean_addMacroScope(v_quotContext_4169_, v___x_4178_, v_currMacroScope_4170_);
v___x_4180_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertDateTime___closed__6));
lean_inc_n(v___x_4175_, 2);
v___x_4181_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4181_, 0, v___x_4175_);
lean_ctor_set(v___x_4181_, 1, v___x_4177_);
lean_ctor_set(v___x_4181_, 2, v___x_4179_);
lean_ctor_set(v___x_4181_, 3, v___x_4180_);
v___x_4182_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_4183_ = l_Lean_Syntax_node2(v___x_4175_, v___x_4182_, v_a_4164_, v___x_4173_);
v___x_4184_ = l_Lean_Syntax_node2(v___x_4175_, v___x_4176_, v___x_4181_, v___x_4183_);
if (v_isShared_4168_ == 0)
{
lean_ctor_set(v___x_4167_, 0, v___x_4184_);
v___x_4186_ = v___x_4167_;
goto v_reusejp_4185_;
}
else
{
lean_object* v_reuseFailAlloc_4187_; 
v_reuseFailAlloc_4187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4187_, 0, v___x_4184_);
lean_ctor_set(v_reuseFailAlloc_4187_, 1, v_a_4165_);
v___x_4186_ = v_reuseFailAlloc_4187_;
goto v_reusejp_4185_;
}
v_reusejp_4185_:
{
return v___x_4186_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termZoned_x28___x2c___x29__1___boxed(lean_object* v_x_4189_, lean_object* v_a_4190_, lean_object* v_a_4191_){
_start:
{
lean_object* v_res_4192_; 
v_res_4192_ = l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termZoned_x28___x2c___x29__1(v_x_4189_, v_a_4190_, v_a_4191_);
lean_dec_ref(v_a_4190_);
return v_res_4192_;
}
}
LEAN_EXPORT lean_object* l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termDatetime_x28___x29__1(lean_object* v_x_4193_, lean_object* v_a_4194_, lean_object* v_a_4195_){
_start:
{
lean_object* v___x_4196_; uint8_t v___x_4197_; 
v___x_4196_ = ((lean_object*)(l_Std_Time_termDatetime_x28___x29___closed__1));
lean_inc(v_x_4193_);
v___x_4197_ = l_Lean_Syntax_isOfKind(v_x_4193_, v___x_4196_);
if (v___x_4197_ == 0)
{
lean_object* v___x_4198_; lean_object* v___x_4199_; 
lean_dec(v_x_4193_);
v___x_4198_ = lean_box(1);
v___x_4199_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4199_, 0, v___x_4198_);
lean_ctor_set(v___x_4199_, 1, v_a_4195_);
return v___x_4199_;
}
else
{
lean_object* v___x_4200_; lean_object* v_date_4201_; lean_object* v___x_4202_; uint8_t v___x_4203_; 
v___x_4200_ = lean_unsigned_to_nat(1u);
v_date_4201_ = l_Lean_Syntax_getArg(v_x_4193_, v___x_4200_);
lean_dec(v_x_4193_);
v___x_4202_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxString___closed__1));
lean_inc(v_date_4201_);
v___x_4203_ = l_Lean_Syntax_isOfKind(v_date_4201_, v___x_4202_);
if (v___x_4203_ == 0)
{
lean_object* v___x_4204_; lean_object* v___x_4205_; 
lean_dec(v_date_4201_);
v___x_4204_ = lean_box(1);
v___x_4205_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4205_, 0, v___x_4204_);
lean_ctor_set(v___x_4205_, 1, v_a_4195_);
return v___x_4205_;
}
else
{
lean_object* v___x_4206_; lean_object* v___x_4207_; 
v___x_4206_ = l_Lean_TSyntax_getString(v_date_4201_);
v___x_4207_ = l_Std_Time_PlainDateTime_fromLeanDateTimeString(v___x_4206_);
if (lean_obj_tag(v___x_4207_) == 0)
{
lean_object* v_a_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; 
v_a_4208_ = lean_ctor_get(v___x_4207_, 0);
lean_inc(v_a_4208_);
lean_dec_ref_known(v___x_4207_, 1);
v___x_4209_ = ((lean_object*)(l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termZoned_x28___x29__1___closed__0));
v___x_4210_ = lean_string_append(v___x_4209_, v_a_4208_);
lean_dec(v_a_4208_);
v___x_4211_ = l_Lean_Macro_throwErrorAt___redArg(v_date_4201_, v___x_4210_, v_a_4194_, v_a_4195_);
lean_dec(v_date_4201_);
return v___x_4211_;
}
else
{
lean_object* v_a_4212_; lean_object* v___x_4213_; lean_object* v_a_4214_; lean_object* v_a_4215_; lean_object* v___x_4217_; uint8_t v_isShared_4218_; uint8_t v_isSharedCheck_4222_; 
lean_dec(v_date_4201_);
v_a_4212_ = lean_ctor_get(v___x_4207_, 0);
lean_inc(v_a_4212_);
lean_dec_ref_known(v___x_4207_, 1);
v___x_4213_ = l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime(v_a_4212_, v_a_4194_, v_a_4195_);
v_a_4214_ = lean_ctor_get(v___x_4213_, 0);
v_a_4215_ = lean_ctor_get(v___x_4213_, 1);
v_isSharedCheck_4222_ = !lean_is_exclusive(v___x_4213_);
if (v_isSharedCheck_4222_ == 0)
{
v___x_4217_ = v___x_4213_;
v_isShared_4218_ = v_isSharedCheck_4222_;
goto v_resetjp_4216_;
}
else
{
lean_inc(v_a_4215_);
lean_inc(v_a_4214_);
lean_dec(v___x_4213_);
v___x_4217_ = lean_box(0);
v_isShared_4218_ = v_isSharedCheck_4222_;
goto v_resetjp_4216_;
}
v_resetjp_4216_:
{
lean_object* v___x_4220_; 
if (v_isShared_4218_ == 0)
{
v___x_4220_ = v___x_4217_;
goto v_reusejp_4219_;
}
else
{
lean_object* v_reuseFailAlloc_4221_; 
v_reuseFailAlloc_4221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4221_, 0, v_a_4214_);
lean_ctor_set(v_reuseFailAlloc_4221_, 1, v_a_4215_);
v___x_4220_ = v_reuseFailAlloc_4221_;
goto v_reusejp_4219_;
}
v_reusejp_4219_:
{
return v___x_4220_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termDatetime_x28___x29__1___boxed(lean_object* v_x_4223_, lean_object* v_a_4224_, lean_object* v_a_4225_){
_start:
{
lean_object* v_res_4226_; 
v_res_4226_ = l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termDatetime_x28___x29__1(v_x_4223_, v_a_4224_, v_a_4225_);
lean_dec_ref(v_a_4224_);
return v_res_4226_;
}
}
LEAN_EXPORT lean_object* l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termDate_x28___x29__1(lean_object* v_x_4227_, lean_object* v_a_4228_, lean_object* v_a_4229_){
_start:
{
lean_object* v___x_4230_; uint8_t v___x_4231_; 
v___x_4230_ = ((lean_object*)(l_Std_Time_termDate_x28___x29___closed__1));
lean_inc(v_x_4227_);
v___x_4231_ = l_Lean_Syntax_isOfKind(v_x_4227_, v___x_4230_);
if (v___x_4231_ == 0)
{
lean_object* v___x_4232_; lean_object* v___x_4233_; 
lean_dec(v_x_4227_);
v___x_4232_ = lean_box(1);
v___x_4233_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4233_, 0, v___x_4232_);
lean_ctor_set(v___x_4233_, 1, v_a_4229_);
return v___x_4233_;
}
else
{
lean_object* v___x_4234_; lean_object* v_date_4235_; lean_object* v___x_4236_; uint8_t v___x_4237_; 
v___x_4234_ = lean_unsigned_to_nat(1u);
v_date_4235_ = l_Lean_Syntax_getArg(v_x_4227_, v___x_4234_);
lean_dec(v_x_4227_);
v___x_4236_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxString___closed__1));
lean_inc(v_date_4235_);
v___x_4237_ = l_Lean_Syntax_isOfKind(v_date_4235_, v___x_4236_);
if (v___x_4237_ == 0)
{
lean_object* v___x_4238_; lean_object* v___x_4239_; 
lean_dec(v_date_4235_);
v___x_4238_ = lean_box(1);
v___x_4239_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4239_, 0, v___x_4238_);
lean_ctor_set(v___x_4239_, 1, v_a_4229_);
return v___x_4239_;
}
else
{
lean_object* v___x_4240_; lean_object* v___x_4241_; 
v___x_4240_ = l_Lean_TSyntax_getString(v_date_4235_);
v___x_4241_ = l_Std_Time_PlainDate_fromSQLDateString(v___x_4240_);
if (lean_obj_tag(v___x_4241_) == 0)
{
lean_object* v_a_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; 
v_a_4242_ = lean_ctor_get(v___x_4241_, 0);
lean_inc(v_a_4242_);
lean_dec_ref_known(v___x_4241_, 1);
v___x_4243_ = ((lean_object*)(l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termZoned_x28___x29__1___closed__0));
v___x_4244_ = lean_string_append(v___x_4243_, v_a_4242_);
lean_dec(v_a_4242_);
v___x_4245_ = l_Lean_Macro_throwErrorAt___redArg(v_date_4235_, v___x_4244_, v_a_4228_, v_a_4229_);
lean_dec(v_date_4235_);
return v___x_4245_;
}
else
{
lean_object* v_a_4246_; lean_object* v___x_4247_; lean_object* v_a_4248_; lean_object* v_a_4249_; lean_object* v___x_4251_; uint8_t v_isShared_4252_; uint8_t v_isSharedCheck_4256_; 
lean_dec(v_date_4235_);
v_a_4246_ = lean_ctor_get(v___x_4241_, 0);
lean_inc(v_a_4246_);
lean_dec_ref_known(v___x_4241_, 1);
v___x_4247_ = l___private_Std_Time_Notation_0__Std_Time_convertPlainDate(v_a_4246_, v_a_4228_, v_a_4229_);
lean_dec(v_a_4246_);
v_a_4248_ = lean_ctor_get(v___x_4247_, 0);
v_a_4249_ = lean_ctor_get(v___x_4247_, 1);
v_isSharedCheck_4256_ = !lean_is_exclusive(v___x_4247_);
if (v_isSharedCheck_4256_ == 0)
{
v___x_4251_ = v___x_4247_;
v_isShared_4252_ = v_isSharedCheck_4256_;
goto v_resetjp_4250_;
}
else
{
lean_inc(v_a_4249_);
lean_inc(v_a_4248_);
lean_dec(v___x_4247_);
v___x_4251_ = lean_box(0);
v_isShared_4252_ = v_isSharedCheck_4256_;
goto v_resetjp_4250_;
}
v_resetjp_4250_:
{
lean_object* v___x_4254_; 
if (v_isShared_4252_ == 0)
{
v___x_4254_ = v___x_4251_;
goto v_reusejp_4253_;
}
else
{
lean_object* v_reuseFailAlloc_4255_; 
v_reuseFailAlloc_4255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4255_, 0, v_a_4248_);
lean_ctor_set(v_reuseFailAlloc_4255_, 1, v_a_4249_);
v___x_4254_ = v_reuseFailAlloc_4255_;
goto v_reusejp_4253_;
}
v_reusejp_4253_:
{
return v___x_4254_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termDate_x28___x29__1___boxed(lean_object* v_x_4257_, lean_object* v_a_4258_, lean_object* v_a_4259_){
_start:
{
lean_object* v_res_4260_; 
v_res_4260_ = l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termDate_x28___x29__1(v_x_4257_, v_a_4258_, v_a_4259_);
lean_dec_ref(v_a_4258_);
return v_res_4260_;
}
}
LEAN_EXPORT lean_object* l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termTime_x28___x29__1(lean_object* v_x_4261_, lean_object* v_a_4262_, lean_object* v_a_4263_){
_start:
{
lean_object* v___x_4264_; uint8_t v___x_4265_; 
v___x_4264_ = ((lean_object*)(l_Std_Time_termTime_x28___x29___closed__1));
lean_inc(v_x_4261_);
v___x_4265_ = l_Lean_Syntax_isOfKind(v_x_4261_, v___x_4264_);
if (v___x_4265_ == 0)
{
lean_object* v___x_4266_; lean_object* v___x_4267_; 
lean_dec(v_x_4261_);
v___x_4266_ = lean_box(1);
v___x_4267_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4267_, 0, v___x_4266_);
lean_ctor_set(v___x_4267_, 1, v_a_4263_);
return v___x_4267_;
}
else
{
lean_object* v___x_4268_; lean_object* v_time_4269_; lean_object* v___x_4270_; uint8_t v___x_4271_; 
v___x_4268_ = lean_unsigned_to_nat(1u);
v_time_4269_ = l_Lean_Syntax_getArg(v_x_4261_, v___x_4268_);
lean_dec(v_x_4261_);
v___x_4270_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxString___closed__1));
lean_inc(v_time_4269_);
v___x_4271_ = l_Lean_Syntax_isOfKind(v_time_4269_, v___x_4270_);
if (v___x_4271_ == 0)
{
lean_object* v___x_4272_; lean_object* v___x_4273_; 
lean_dec(v_time_4269_);
v___x_4272_ = lean_box(1);
v___x_4273_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4273_, 0, v___x_4272_);
lean_ctor_set(v___x_4273_, 1, v_a_4263_);
return v___x_4273_;
}
else
{
lean_object* v___x_4274_; lean_object* v___x_4275_; 
v___x_4274_ = l_Lean_TSyntax_getString(v_time_4269_);
v___x_4275_ = l_Std_Time_PlainTime_fromLeanTime24Hour(v___x_4274_);
if (lean_obj_tag(v___x_4275_) == 0)
{
lean_object* v_a_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; 
v_a_4276_ = lean_ctor_get(v___x_4275_, 0);
lean_inc(v_a_4276_);
lean_dec_ref_known(v___x_4275_, 1);
v___x_4277_ = ((lean_object*)(l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termZoned_x28___x29__1___closed__0));
v___x_4278_ = lean_string_append(v___x_4277_, v_a_4276_);
lean_dec(v_a_4276_);
v___x_4279_ = l_Lean_Macro_throwErrorAt___redArg(v_time_4269_, v___x_4278_, v_a_4262_, v_a_4263_);
lean_dec(v_time_4269_);
return v___x_4279_;
}
else
{
lean_object* v_a_4280_; lean_object* v___x_4281_; lean_object* v_a_4282_; lean_object* v_a_4283_; lean_object* v___x_4285_; uint8_t v_isShared_4286_; uint8_t v_isSharedCheck_4290_; 
lean_dec(v_time_4269_);
v_a_4280_ = lean_ctor_get(v___x_4275_, 0);
lean_inc(v_a_4280_);
lean_dec_ref_known(v___x_4275_, 1);
v___x_4281_ = l___private_Std_Time_Notation_0__Std_Time_convertPlainTime(v_a_4280_, v_a_4262_, v_a_4263_);
v_a_4282_ = lean_ctor_get(v___x_4281_, 0);
v_a_4283_ = lean_ctor_get(v___x_4281_, 1);
v_isSharedCheck_4290_ = !lean_is_exclusive(v___x_4281_);
if (v_isSharedCheck_4290_ == 0)
{
v___x_4285_ = v___x_4281_;
v_isShared_4286_ = v_isSharedCheck_4290_;
goto v_resetjp_4284_;
}
else
{
lean_inc(v_a_4283_);
lean_inc(v_a_4282_);
lean_dec(v___x_4281_);
v___x_4285_ = lean_box(0);
v_isShared_4286_ = v_isSharedCheck_4290_;
goto v_resetjp_4284_;
}
v_resetjp_4284_:
{
lean_object* v___x_4288_; 
if (v_isShared_4286_ == 0)
{
v___x_4288_ = v___x_4285_;
goto v_reusejp_4287_;
}
else
{
lean_object* v_reuseFailAlloc_4289_; 
v_reuseFailAlloc_4289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4289_, 0, v_a_4282_);
lean_ctor_set(v_reuseFailAlloc_4289_, 1, v_a_4283_);
v___x_4288_ = v_reuseFailAlloc_4289_;
goto v_reusejp_4287_;
}
v_reusejp_4287_:
{
return v___x_4288_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termTime_x28___x29__1___boxed(lean_object* v_x_4291_, lean_object* v_a_4292_, lean_object* v_a_4293_){
_start:
{
lean_object* v_res_4294_; 
v_res_4294_ = l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termTime_x28___x29__1(v_x_4291_, v_a_4292_, v_a_4293_);
lean_dec_ref(v_a_4292_);
return v_res_4294_;
}
}
LEAN_EXPORT lean_object* l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termOffset_x28___x29__1(lean_object* v_x_4295_, lean_object* v_a_4296_, lean_object* v_a_4297_){
_start:
{
lean_object* v___x_4298_; uint8_t v___x_4299_; 
v___x_4298_ = ((lean_object*)(l_Std_Time_termOffset_x28___x29___closed__1));
lean_inc(v_x_4295_);
v___x_4299_ = l_Lean_Syntax_isOfKind(v_x_4295_, v___x_4298_);
if (v___x_4299_ == 0)
{
lean_object* v___x_4300_; lean_object* v___x_4301_; 
lean_dec(v_x_4295_);
v___x_4300_ = lean_box(1);
v___x_4301_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4301_, 0, v___x_4300_);
lean_ctor_set(v___x_4301_, 1, v_a_4297_);
return v___x_4301_;
}
else
{
lean_object* v___x_4302_; lean_object* v_offset_4303_; lean_object* v___x_4304_; uint8_t v___x_4305_; 
v___x_4302_ = lean_unsigned_to_nat(1u);
v_offset_4303_ = l_Lean_Syntax_getArg(v_x_4295_, v___x_4302_);
lean_dec(v_x_4295_);
v___x_4304_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxString___closed__1));
lean_inc(v_offset_4303_);
v___x_4305_ = l_Lean_Syntax_isOfKind(v_offset_4303_, v___x_4304_);
if (v___x_4305_ == 0)
{
lean_object* v___x_4306_; lean_object* v___x_4307_; 
lean_dec(v_offset_4303_);
v___x_4306_ = lean_box(1);
v___x_4307_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4307_, 0, v___x_4306_);
lean_ctor_set(v___x_4307_, 1, v_a_4297_);
return v___x_4307_;
}
else
{
lean_object* v___x_4308_; lean_object* v___x_4309_; 
v___x_4308_ = l_Lean_TSyntax_getString(v_offset_4303_);
v___x_4309_ = l_Std_Time_TimeZone_Offset_fromOffset(v___x_4308_);
if (lean_obj_tag(v___x_4309_) == 0)
{
lean_object* v_a_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; 
v_a_4310_ = lean_ctor_get(v___x_4309_, 0);
lean_inc(v_a_4310_);
lean_dec_ref_known(v___x_4309_, 1);
v___x_4311_ = ((lean_object*)(l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termZoned_x28___x29__1___closed__0));
v___x_4312_ = lean_string_append(v___x_4311_, v_a_4310_);
lean_dec(v_a_4310_);
v___x_4313_ = l_Lean_Macro_throwErrorAt___redArg(v_offset_4303_, v___x_4312_, v_a_4296_, v_a_4297_);
lean_dec(v_offset_4303_);
return v___x_4313_;
}
else
{
lean_object* v_a_4314_; lean_object* v___x_4315_; lean_object* v_a_4316_; lean_object* v_a_4317_; lean_object* v___x_4319_; uint8_t v_isShared_4320_; uint8_t v_isSharedCheck_4324_; 
lean_dec(v_offset_4303_);
v_a_4314_ = lean_ctor_get(v___x_4309_, 0);
lean_inc(v_a_4314_);
lean_dec_ref_known(v___x_4309_, 1);
v___x_4315_ = l___private_Std_Time_Notation_0__Std_Time_convertOffset(v_a_4314_, v_a_4296_, v_a_4297_);
lean_dec(v_a_4314_);
v_a_4316_ = lean_ctor_get(v___x_4315_, 0);
v_a_4317_ = lean_ctor_get(v___x_4315_, 1);
v_isSharedCheck_4324_ = !lean_is_exclusive(v___x_4315_);
if (v_isSharedCheck_4324_ == 0)
{
v___x_4319_ = v___x_4315_;
v_isShared_4320_ = v_isSharedCheck_4324_;
goto v_resetjp_4318_;
}
else
{
lean_inc(v_a_4317_);
lean_inc(v_a_4316_);
lean_dec(v___x_4315_);
v___x_4319_ = lean_box(0);
v_isShared_4320_ = v_isSharedCheck_4324_;
goto v_resetjp_4318_;
}
v_resetjp_4318_:
{
lean_object* v___x_4322_; 
if (v_isShared_4320_ == 0)
{
v___x_4322_ = v___x_4319_;
goto v_reusejp_4321_;
}
else
{
lean_object* v_reuseFailAlloc_4323_; 
v_reuseFailAlloc_4323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4323_, 0, v_a_4316_);
lean_ctor_set(v_reuseFailAlloc_4323_, 1, v_a_4317_);
v___x_4322_ = v_reuseFailAlloc_4323_;
goto v_reusejp_4321_;
}
v_reusejp_4321_:
{
return v___x_4322_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termOffset_x28___x29__1___boxed(lean_object* v_x_4325_, lean_object* v_a_4326_, lean_object* v_a_4327_){
_start:
{
lean_object* v_res_4328_; 
v_res_4328_ = l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termOffset_x28___x29__1(v_x_4325_, v_a_4326_, v_a_4327_);
lean_dec_ref(v_a_4326_);
return v_res_4328_;
}
}
LEAN_EXPORT lean_object* l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termTimezone_x28___x29__1(lean_object* v_x_4329_, lean_object* v_a_4330_, lean_object* v_a_4331_){
_start:
{
lean_object* v___x_4332_; uint8_t v___x_4333_; 
v___x_4332_ = ((lean_object*)(l_Std_Time_termTimezone_x28___x29___closed__1));
lean_inc(v_x_4329_);
v___x_4333_ = l_Lean_Syntax_isOfKind(v_x_4329_, v___x_4332_);
if (v___x_4333_ == 0)
{
lean_object* v___x_4334_; lean_object* v___x_4335_; 
lean_dec(v_x_4329_);
v___x_4334_ = lean_box(1);
v___x_4335_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4335_, 0, v___x_4334_);
lean_ctor_set(v___x_4335_, 1, v_a_4331_);
return v___x_4335_;
}
else
{
lean_object* v___x_4336_; lean_object* v_tz_4337_; lean_object* v___x_4338_; uint8_t v___x_4339_; 
v___x_4336_ = lean_unsigned_to_nat(1u);
v_tz_4337_ = l_Lean_Syntax_getArg(v_x_4329_, v___x_4336_);
lean_dec(v_x_4329_);
v___x_4338_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxString___closed__1));
lean_inc(v_tz_4337_);
v___x_4339_ = l_Lean_Syntax_isOfKind(v_tz_4337_, v___x_4338_);
if (v___x_4339_ == 0)
{
lean_object* v___x_4340_; lean_object* v___x_4341_; 
lean_dec(v_tz_4337_);
v___x_4340_ = lean_box(1);
v___x_4341_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4341_, 0, v___x_4340_);
lean_ctor_set(v___x_4341_, 1, v_a_4331_);
return v___x_4341_;
}
else
{
lean_object* v___x_4342_; lean_object* v___x_4343_; 
v___x_4342_ = l_Lean_TSyntax_getString(v_tz_4337_);
v___x_4343_ = l_Std_Time_TimeZone_fromTimeZone(v___x_4342_);
if (lean_obj_tag(v___x_4343_) == 0)
{
lean_object* v_a_4344_; lean_object* v___x_4345_; lean_object* v___x_4346_; lean_object* v___x_4347_; 
v_a_4344_ = lean_ctor_get(v___x_4343_, 0);
lean_inc(v_a_4344_);
lean_dec_ref_known(v___x_4343_, 1);
v___x_4345_ = ((lean_object*)(l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termZoned_x28___x29__1___closed__0));
v___x_4346_ = lean_string_append(v___x_4345_, v_a_4344_);
lean_dec(v_a_4344_);
v___x_4347_ = l_Lean_Macro_throwErrorAt___redArg(v_tz_4337_, v___x_4346_, v_a_4330_, v_a_4331_);
lean_dec(v_tz_4337_);
return v___x_4347_;
}
else
{
lean_object* v_a_4348_; lean_object* v___x_4349_; lean_object* v_a_4350_; lean_object* v_a_4351_; lean_object* v___x_4353_; uint8_t v_isShared_4354_; uint8_t v_isSharedCheck_4358_; 
lean_dec(v_tz_4337_);
v_a_4348_ = lean_ctor_get(v___x_4343_, 0);
lean_inc(v_a_4348_);
lean_dec_ref_known(v___x_4343_, 1);
v___x_4349_ = l___private_Std_Time_Notation_0__Std_Time_convertTimezone(v_a_4348_, v_a_4330_, v_a_4331_);
v_a_4350_ = lean_ctor_get(v___x_4349_, 0);
v_a_4351_ = lean_ctor_get(v___x_4349_, 1);
v_isSharedCheck_4358_ = !lean_is_exclusive(v___x_4349_);
if (v_isSharedCheck_4358_ == 0)
{
v___x_4353_ = v___x_4349_;
v_isShared_4354_ = v_isSharedCheck_4358_;
goto v_resetjp_4352_;
}
else
{
lean_inc(v_a_4351_);
lean_inc(v_a_4350_);
lean_dec(v___x_4349_);
v___x_4353_ = lean_box(0);
v_isShared_4354_ = v_isSharedCheck_4358_;
goto v_resetjp_4352_;
}
v_resetjp_4352_:
{
lean_object* v___x_4356_; 
if (v_isShared_4354_ == 0)
{
v___x_4356_ = v___x_4353_;
goto v_reusejp_4355_;
}
else
{
lean_object* v_reuseFailAlloc_4357_; 
v_reuseFailAlloc_4357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4357_, 0, v_a_4350_);
lean_ctor_set(v_reuseFailAlloc_4357_, 1, v_a_4351_);
v___x_4356_ = v_reuseFailAlloc_4357_;
goto v_reusejp_4355_;
}
v_reusejp_4355_:
{
return v___x_4356_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termTimezone_x28___x29__1___boxed(lean_object* v_x_4359_, lean_object* v_a_4360_, lean_object* v_a_4361_){
_start:
{
lean_object* v_res_4362_; 
v_res_4362_ = l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termTimezone_x28___x29__1(v_x_4359_, v_a_4360_, v_a_4361_);
lean_dec_ref(v_a_4360_);
return v_res_4362_;
}
}
lean_object* runtime_initialize_Std_Time_Format(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Time_Notation(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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

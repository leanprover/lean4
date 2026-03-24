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
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_thunk_get_own(lean_object*);
lean_object* l_Std_Time_ZonedDateTime_fromLeanDateTimeWithZoneString(lean_object*);
lean_object* l_Std_Time_ZonedDateTime_fromLeanDateTimeWithIdentifierString(lean_object*);
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
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Std.Time.Modifier.MorL"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__33 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__33_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__34;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "MorL"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__35 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__35_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__36_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__36_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__36_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__36_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__36_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__36_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__35_value),LEAN_SCALAR_PTR_LITERAL(187, 73, 66, 86, 160, 81, 156, 182)}};
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
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.d"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__76 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__76_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__77_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__77;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__78_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "d"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__78 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__78_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__79_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__79_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__79_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__79_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__79_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__79_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__78_value),LEAN_SCALAR_PTR_LITERAL(43, 177, 95, 132, 207, 75, 80, 59)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__79 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__79_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__80_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__79_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__80 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__80_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__81_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__79_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__81 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__81_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__82_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__81_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__82 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__82_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__83_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__80_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__82_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__83 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__83_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__84_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Std.Time.Modifier.Qorq"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__84 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__84_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__85_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__85;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__86_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Qorq"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__86 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__86_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__87_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__87_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__87_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__87_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__87_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__87_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__87_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__86_value),LEAN_SCALAR_PTR_LITERAL(239, 139, 79, 232, 51, 16, 131, 46)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__87 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__87_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__88_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__87_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__88 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__88_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__89_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__87_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__89 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__89_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__90_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__89_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__90 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__90_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__91_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__88_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__90_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__91 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__91_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__92_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.w"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__92 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__92_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__93_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__93;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__94_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "w"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__94 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__94_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__95_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__95_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__95_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__95_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__95_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__95_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__95_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__94_value),LEAN_SCALAR_PTR_LITERAL(109, 122, 115, 3, 58, 174, 210, 61)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__95 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__95_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__96_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__95_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__96 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__96_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__97_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__95_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__97 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__97_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__98_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__97_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__98 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__98_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__99_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__96_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__98_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__99 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__99_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__100_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.W"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__100 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__100_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__101_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__101;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__102_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "W"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__102 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__102_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__103_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__103_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__103_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__103_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__103_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__103_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__103_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__102_value),LEAN_SCALAR_PTR_LITERAL(142, 210, 249, 219, 201, 68, 141, 242)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__103 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__103_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__104_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__103_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__104 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__104_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__105_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__103_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__105 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__105_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__106_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__105_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__106 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__106_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__107_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__104_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__106_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__107 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__107_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__108_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.E"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__108 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__108_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__109_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__109;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__110_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "E"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__110 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__110_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__111_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__111_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__111_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__111_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__111_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__111_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__111_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__110_value),LEAN_SCALAR_PTR_LITERAL(221, 114, 205, 107, 57, 101, 237, 55)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__111 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__111_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__112_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__111_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__112 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__112_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__113_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__111_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__113 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__113_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__114_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__113_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__114 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__114_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__115_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__112_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__114_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__115 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__115_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__116_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Std.Time.Modifier.eorc"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__116 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__116_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__117_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__117;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__118_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "eorc"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__118 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__118_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__119_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__119_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__119_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__119_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__119_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__119_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__119_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__118_value),LEAN_SCALAR_PTR_LITERAL(158, 189, 225, 255, 240, 175, 155, 162)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__119 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__119_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__120_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__119_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__120 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__120_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__121_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__119_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__121 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__121_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__122_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__121_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__122 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__122_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__123_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__120_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__122_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__123 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__123_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__124_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.F"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__124 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__124_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__125_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__125;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__126_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "F"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__126 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__126_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__127_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__127_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__127_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__127_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__127_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__127_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__127_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__126_value),LEAN_SCALAR_PTR_LITERAL(255, 172, 252, 76, 184, 53, 176, 25)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__127 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__127_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__128_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__127_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__128 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__128_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__129_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__127_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__129 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__129_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__130_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__129_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__130 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__130_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__131_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__128_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__130_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__131 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__131_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__132_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.a"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__132 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__132_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__133_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__133;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__134_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "a"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__134 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__134_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__135_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__135_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__135_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__135_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__135_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__135_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__135_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__134_value),LEAN_SCALAR_PTR_LITERAL(36, 69, 244, 234, 150, 73, 242, 198)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__135 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__135_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__136_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__135_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__136 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__136_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__137_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__135_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__137 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__137_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__138_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__137_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__138 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__138_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__139_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__136_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__138_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__139 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__139_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__140_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.h"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__140 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__140_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__141_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__141;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__142_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__142 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__142_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__143_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__143_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__143_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__143_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__143_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__143_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__143_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__142_value),LEAN_SCALAR_PTR_LITERAL(171, 19, 0, 95, 105, 8, 122, 135)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__143 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__143_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__144_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__143_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__144 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__144_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__145_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__143_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__145 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__145_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__146_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__145_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__146 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__146_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__147_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__144_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__146_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__147 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__147_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__148_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.K"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__148 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__148_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__149_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__149;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__150_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "K"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__150 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__150_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__151_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__151_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__151_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__151_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__151_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__151_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__151_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__150_value),LEAN_SCALAR_PTR_LITERAL(175, 237, 107, 230, 188, 207, 116, 239)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__151 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__151_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__152_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__151_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__152 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__152_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__153_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__151_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__153 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__153_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__154_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__153_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__154 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__154_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__155_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__152_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__154_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__155 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__155_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__156_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.k"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__156 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__156_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__157_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__157;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__158_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "k"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__158 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__158_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__159_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__159_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__159_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__159_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__159_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__159_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__159_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__158_value),LEAN_SCALAR_PTR_LITERAL(186, 55, 92, 94, 160, 8, 215, 223)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__159 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__159_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__160_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__159_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__160 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__160_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__161_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__159_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__161 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__161_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__162_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__161_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__162 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__162_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__163_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__160_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__162_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__163 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__163_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__164_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.H"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__164 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__164_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__165_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__165;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__166_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "H"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__166 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__166_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__167_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__167_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__167_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__167_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__167_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__167_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__167_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__166_value),LEAN_SCALAR_PTR_LITERAL(202, 31, 161, 0, 128, 16, 18, 169)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__167 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__167_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__168_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__167_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__168 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__168_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__169_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__167_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__169 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__169_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__170_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__169_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__170 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__170_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__171_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__168_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__170_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__171 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__171_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__172_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.m"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__172 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__172_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__173_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__173;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__174_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "m"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__174 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__174_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__175_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__175_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__175_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__175_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__175_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__175_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__175_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__174_value),LEAN_SCALAR_PTR_LITERAL(118, 254, 173, 99, 0, 222, 89, 33)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__175 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__175_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__176_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__175_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__176 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__176_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__177_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__175_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__177 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__177_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__178_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__177_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__178 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__178_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__179_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__176_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__178_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__179 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__179_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__180_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.s"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__180 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__180_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__181_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__181;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__182_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "s"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__182 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__182_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__183_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__183_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__183_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__183_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__183_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__183_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__183_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__182_value),LEAN_SCALAR_PTR_LITERAL(80, 170, 75, 145, 176, 122, 31, 111)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__183 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__183_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__184_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__183_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__184 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__184_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__185_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__183_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__185 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__185_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__186_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__185_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__186 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__186_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__187_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__184_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__186_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__187 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__187_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__188_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.S"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__188 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__188_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__189_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__189;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__190_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "S"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__190 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__190_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__191_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__191_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__191_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__191_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__191_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__191_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__191_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__190_value),LEAN_SCALAR_PTR_LITERAL(61, 110, 227, 5, 165, 49, 182, 207)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__191 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__191_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__192_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__191_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__192 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__192_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__193_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__191_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__193 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__193_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__194_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__193_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__194 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__194_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__195_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__192_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__194_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__195 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__195_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__196_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.A"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__196 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__196_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__197_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__197;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__198_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "A"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__198 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__198_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__199_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__199_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__199_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__199_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__199_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__199_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__199_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__198_value),LEAN_SCALAR_PTR_LITERAL(254, 42, 156, 100, 183, 179, 31, 180)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__199 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__199_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__200_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__199_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__200 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__200_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__201_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__199_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__201 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__201_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__202_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__201_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__202 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__202_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__203_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__200_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__202_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__203 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__203_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__204_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.n"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__204 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__204_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__205_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__205;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__206_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "n"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__206 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__206_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__207_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__207_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__207_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__207_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__207_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__207_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__207_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__206_value),LEAN_SCALAR_PTR_LITERAL(38, 78, 251, 143, 117, 169, 85, 233)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__207 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__207_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__208_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__207_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__208 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__208_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__209_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__207_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__209 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__209_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__210_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__209_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__210 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__210_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__211_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__208_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__210_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__211 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__211_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__212_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.N"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__212 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__212_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__213_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__213;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__214_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "N"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__214 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__214_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__215_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__215_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__215_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__215_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__215_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__215_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__215_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__214_value),LEAN_SCALAR_PTR_LITERAL(139, 9, 15, 62, 231, 211, 146, 60)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__215 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__215_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__216_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__215_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__216 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__216_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__217_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__215_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__217 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__217_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__218_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__217_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__218 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__218_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__219_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__216_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__218_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__219 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__219_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__220_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.V"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__220 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__220_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__221_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__221;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__222_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "V"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__222 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__222_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__223_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__223_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__223_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__223_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__223_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__223_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__223_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__222_value),LEAN_SCALAR_PTR_LITERAL(49, 190, 37, 135, 7, 5, 128, 4)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__223 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__223_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__224_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__223_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__224 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__224_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__225_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__223_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__225 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__225_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__226_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__225_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__226 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__226_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__227_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__224_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__226_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__227 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__227_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__228_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.z"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__228 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__228_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__229_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__229;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__230_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "z"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__230 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__230_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__231_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__231_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__231_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__231_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__231_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__231_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__231_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__230_value),LEAN_SCALAR_PTR_LITERAL(181, 218, 97, 100, 129, 163, 177, 227)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__231 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__231_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__232_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__231_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__232 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__232_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__233_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__231_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__233 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__233_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__234_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__233_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__234 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__234_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__235_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__232_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__234_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__235 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__235_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__236_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.O"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__236 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__236_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__237_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__237;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__238_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "O"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__238 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__238_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__239_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__239_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__239_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__239_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__239_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__239_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__239_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__238_value),LEAN_SCALAR_PTR_LITERAL(58, 151, 205, 45, 234, 213, 167, 33)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__239 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__239_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__240_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__239_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__240 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__240_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__241_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__239_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__241 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__241_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__242_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__241_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__242 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__242_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__243_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__240_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__242_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__243 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__243_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__244_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.X"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__244 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__244_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__245_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__245;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__246_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "X"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__246 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__246_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__247_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__247_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__247_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__247_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__247_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__247_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__247_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__246_value),LEAN_SCALAR_PTR_LITERAL(26, 41, 196, 142, 13, 161, 206, 121)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__247 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__247_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__248_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__247_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__248 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__248_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__249_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__247_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__249 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__249_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__250_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__249_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__250 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__250_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__251_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__248_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__250_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__251 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__251_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__252_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.x"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__252 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__252_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__253_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__253;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__254_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__254 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__254_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__255_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__255_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__255_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__255_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__255_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__255_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__255_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__254_value),LEAN_SCALAR_PTR_LITERAL(200, 2, 62, 177, 15, 17, 219, 69)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__255 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__255_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__256_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__255_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__256 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__256_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__257_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__255_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__257 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__257_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__258_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__257_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__258 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__258_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__259_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__256_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__258_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__259 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__259_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__260_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.Z"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__260 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__260_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__261_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__261;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__262_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "Z"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__262 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__262_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__263_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__263_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__263_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__263_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__263_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__263_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__263_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__262_value),LEAN_SCALAR_PTR_LITERAL(44, 18, 171, 9, 22, 243, 82, 66)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__263 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__263_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__264_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__263_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__264 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__264_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__265_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__263_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__265 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__265_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__266_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__265_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__266 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__266_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__267_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__264_value),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__266_value)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__267 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__267_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier(lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "Std.Time.ZonedDateTime.ofPlainDateTime"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__0 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__0_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__1;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "ZonedDateTime"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__2 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__2_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "ofPlainDateTime"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__3 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__3_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__4_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__4_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__2_value),LEAN_SCALAR_PTR_LITERAL(10, 243, 83, 19, 38, 113, 64, 216)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__4_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 237, 53, 86, 141, 81, 238, 190)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__4 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__4_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__5 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__5_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__6 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__6_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "Std.Time.TimeZone.ZoneRules.ofTimeZone"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__7 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__7_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__8;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "ZoneRules"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__9 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__9_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "ofTimeZone"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__10 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__10_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__11_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__11_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertOffset___closed__2_value),LEAN_SCALAR_PTR_LITERAL(123, 220, 54, 93, 124, 163, 52, 156)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__11_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__11_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__9_value),LEAN_SCALAR_PTR_LITERAL(195, 137, 30, 162, 40, 87, 69, 227)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__11_value_aux_3),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__10_value),LEAN_SCALAR_PTR_LITERAL(63, 246, 142, 47, 38, 113, 110, 12)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__11 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__11_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__11_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__12 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__12_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__12_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__13 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__13_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "<$>"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__14 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__14_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Database"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__15 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__15_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "defaultGetZoneRules"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__16 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__16_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__17_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__17_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__15_value),LEAN_SCALAR_PTR_LITERAL(52, 29, 11, 135, 198, 98, 142, 215)}};
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__17_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__16_value),LEAN_SCALAR_PTR_LITERAL(195, 204, 158, 115, 111, 241, 211, 242)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__17 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__17_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "term_<$>_"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__18 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__18_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__18_value),LEAN_SCALAR_PTR_LITERAL(128, 74, 67, 119, 243, 145, 72, 28)}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__19 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__19_value;
static const lean_string_object l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Std.Time.Database.defaultGetZoneRules"};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__20 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__20_value;
static lean_once_cell_t l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__21;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__17_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__22 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__22_value;
static const lean_ctor_object l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__22_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__23 = (const lean_object*)&l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__23_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_inc(v_quotContext_67_);
v_currMacroScope_68_ = lean_ctor_get(v_a_65_, 2);
lean_inc(v_currMacroScope_68_);
v_ref_69_ = lean_ctor_get(v_a_65_, 5);
lean_inc(v_ref_69_);
lean_dec_ref(v_a_65_);
v___x_70_ = 0;
v___x_71_ = l_Lean_SourceInfo_fromRef(v_ref_69_, v___x_70_);
lean_dec(v_ref_69_);
v___x_72_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__1, &l___private_Std_Time_Notation_0__Std_Time_convertText___closed__1_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertText___closed__1);
v___x_73_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertText___closed__6));
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
lean_inc(v_quotContext_78_);
v_currMacroScope_79_ = lean_ctor_get(v_a_65_, 2);
lean_inc(v_currMacroScope_79_);
v_ref_80_ = lean_ctor_get(v_a_65_, 5);
lean_inc(v_ref_80_);
lean_dec_ref(v_a_65_);
v___x_81_ = 0;
v___x_82_ = l_Lean_SourceInfo_fromRef(v_ref_80_, v___x_81_);
lean_dec(v_ref_80_);
v___x_83_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__12, &l___private_Std_Time_Notation_0__Std_Time_convertText___closed__12_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertText___closed__12);
v___x_84_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertText___closed__14));
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
lean_inc(v_quotContext_89_);
v_currMacroScope_90_ = lean_ctor_get(v_a_65_, 2);
lean_inc(v_currMacroScope_90_);
v_ref_91_ = lean_ctor_get(v_a_65_, 5);
lean_inc(v_ref_91_);
lean_dec_ref(v_a_65_);
v___x_92_ = 0;
v___x_93_ = l_Lean_SourceInfo_fromRef(v_ref_91_, v___x_92_);
lean_dec(v_ref_91_);
v___x_94_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertText___closed__20, &l___private_Std_Time_Notation_0__Std_Time_convertText___closed__20_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertText___closed__20);
v___x_95_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertText___closed__22));
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
uint8_t v_x_4038__boxed_103_; lean_object* v_res_104_; 
v_x_4038__boxed_103_ = lean_unbox(v_x_100_);
v_res_104_ = l___private_Std_Time_Notation_0__Std_Time_convertText(v_x_4038__boxed_103_, v_a_101_, v_a_102_);
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
lean_inc(v_quotContext_141_);
v_currMacroScope_142_ = lean_ctor_get(v_a_139_, 2);
lean_inc(v_currMacroScope_142_);
v_ref_143_ = lean_ctor_get(v_a_139_, 5);
lean_inc(v_ref_143_);
lean_dec_ref(v_a_139_);
v___x_144_ = 0;
v___x_145_ = l_Lean_SourceInfo_fromRef(v_ref_143_, v___x_144_);
lean_dec(v_ref_143_);
v___x_146_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_147_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__6, &l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__6_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__6);
v___x_148_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__9));
v___x_149_ = l_Lean_addMacroScope(v_quotContext_141_, v___x_148_, v_currMacroScope_142_);
v___x_150_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__13));
lean_inc(v___x_145_);
v___x_151_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_151_, 0, v___x_145_);
lean_ctor_set(v___x_151_, 1, v___x_147_);
lean_ctor_set(v___x_151_, 2, v___x_149_);
lean_ctor_set(v___x_151_, 3, v___x_150_);
v___x_152_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_153_ = l_Nat_reprFast(v_x_138_);
v___x_154_ = lean_box(2);
v___x_155_ = l_Lean_Syntax_mkNumLit(v___x_153_, v___x_154_);
lean_inc(v___x_145_);
v___x_156_ = l_Lean_Syntax_node1(v___x_145_, v___x_152_, v___x_155_);
v___x_157_ = l_Lean_Syntax_node2(v___x_145_, v___x_146_, v___x_151_, v___x_156_);
v___x_158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_158_, 0, v___x_157_);
lean_ctor_set(v___x_158_, 1, v_a_140_);
return v___x_158_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__1(void){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_160_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__0));
v___x_161_ = l_String_toRawSubstring_x27(v___x_160_);
return v___x_161_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__10(void){
_start:
{
lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_181_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__9));
v___x_182_ = l_String_toRawSubstring_x27(v___x_181_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertFraction(lean_object* v_x_200_, lean_object* v_a_201_, lean_object* v_a_202_){
_start:
{
if (lean_obj_tag(v_x_200_) == 0)
{
lean_object* v_quotContext_203_; lean_object* v_currMacroScope_204_; lean_object* v_ref_205_; uint8_t v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v_quotContext_203_ = lean_ctor_get(v_a_201_, 1);
lean_inc(v_quotContext_203_);
v_currMacroScope_204_ = lean_ctor_get(v_a_201_, 2);
lean_inc(v_currMacroScope_204_);
v_ref_205_ = lean_ctor_get(v_a_201_, 5);
lean_inc(v_ref_205_);
lean_dec_ref(v_a_201_);
v___x_206_ = 0;
v___x_207_ = l_Lean_SourceInfo_fromRef(v_ref_205_, v___x_206_);
lean_dec(v_ref_205_);
v___x_208_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__1, &l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__1_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__1);
v___x_209_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__4));
v___x_210_ = l_Lean_addMacroScope(v_quotContext_203_, v___x_209_, v_currMacroScope_204_);
v___x_211_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__8));
v___x_212_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_212_, 0, v___x_207_);
lean_ctor_set(v___x_212_, 1, v___x_208_);
lean_ctor_set(v___x_212_, 2, v___x_210_);
lean_ctor_set(v___x_212_, 3, v___x_211_);
v___x_213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_213_, 0, v___x_212_);
lean_ctor_set(v___x_213_, 1, v_a_202_);
return v___x_213_;
}
else
{
lean_object* v_digits_214_; lean_object* v_quotContext_215_; lean_object* v_currMacroScope_216_; lean_object* v_ref_217_; uint8_t v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v_digits_214_ = lean_ctor_get(v_x_200_, 0);
lean_inc(v_digits_214_);
lean_dec_ref(v_x_200_);
v_quotContext_215_ = lean_ctor_get(v_a_201_, 1);
lean_inc(v_quotContext_215_);
v_currMacroScope_216_ = lean_ctor_get(v_a_201_, 2);
lean_inc(v_currMacroScope_216_);
v_ref_217_ = lean_ctor_get(v_a_201_, 5);
lean_inc(v_ref_217_);
lean_dec_ref(v_a_201_);
v___x_218_ = 0;
v___x_219_ = l_Lean_SourceInfo_fromRef(v_ref_217_, v___x_218_);
lean_dec(v_ref_217_);
v___x_220_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_221_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__10, &l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__10_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__10);
v___x_222_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__12));
v___x_223_ = l_Lean_addMacroScope(v_quotContext_215_, v___x_222_, v_currMacroScope_216_);
v___x_224_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertFraction___closed__16));
lean_inc(v___x_219_);
v___x_225_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_225_, 0, v___x_219_);
lean_ctor_set(v___x_225_, 1, v___x_221_);
lean_ctor_set(v___x_225_, 2, v___x_223_);
lean_ctor_set(v___x_225_, 3, v___x_224_);
v___x_226_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_227_ = l_Nat_reprFast(v_digits_214_);
v___x_228_ = lean_box(2);
v___x_229_ = l_Lean_Syntax_mkNumLit(v___x_227_, v___x_228_);
lean_inc(v___x_219_);
v___x_230_ = l_Lean_Syntax_node1(v___x_219_, v___x_226_, v___x_229_);
v___x_231_ = l_Lean_Syntax_node2(v___x_219_, v___x_220_, v___x_225_, v___x_230_);
v___x_232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_232_, 0, v___x_231_);
lean_ctor_set(v___x_232_, 1, v_a_202_);
return v___x_232_;
}
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__1(void){
_start:
{
lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_234_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__0));
v___x_235_ = l_String_toRawSubstring_x27(v___x_234_);
return v___x_235_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__10(void){
_start:
{
lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_255_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__9));
v___x_256_ = l_String_toRawSubstring_x27(v___x_255_);
return v___x_256_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__18(void){
_start:
{
lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_275_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__17));
v___x_276_ = l_String_toRawSubstring_x27(v___x_275_);
return v___x_276_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__26(void){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_295_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__25));
v___x_296_ = l_String_toRawSubstring_x27(v___x_295_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertYear(lean_object* v_x_314_, lean_object* v_a_315_, lean_object* v_a_316_){
_start:
{
switch(lean_obj_tag(v_x_314_))
{
case 0:
{
lean_object* v_quotContext_317_; lean_object* v_currMacroScope_318_; lean_object* v_ref_319_; uint8_t v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
v_quotContext_317_ = lean_ctor_get(v_a_315_, 1);
lean_inc(v_quotContext_317_);
v_currMacroScope_318_ = lean_ctor_get(v_a_315_, 2);
lean_inc(v_currMacroScope_318_);
v_ref_319_ = lean_ctor_get(v_a_315_, 5);
lean_inc(v_ref_319_);
lean_dec_ref(v_a_315_);
v___x_320_ = 0;
v___x_321_ = l_Lean_SourceInfo_fromRef(v_ref_319_, v___x_320_);
lean_dec(v_ref_319_);
v___x_322_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__1, &l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__1_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__1);
v___x_323_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__4));
v___x_324_ = l_Lean_addMacroScope(v_quotContext_317_, v___x_323_, v_currMacroScope_318_);
v___x_325_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__8));
v___x_326_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_326_, 0, v___x_321_);
lean_ctor_set(v___x_326_, 1, v___x_322_);
lean_ctor_set(v___x_326_, 2, v___x_324_);
lean_ctor_set(v___x_326_, 3, v___x_325_);
v___x_327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_327_, 0, v___x_326_);
lean_ctor_set(v___x_327_, 1, v_a_316_);
return v___x_327_;
}
case 1:
{
lean_object* v_quotContext_328_; lean_object* v_currMacroScope_329_; lean_object* v_ref_330_; uint8_t v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v_quotContext_328_ = lean_ctor_get(v_a_315_, 1);
lean_inc(v_quotContext_328_);
v_currMacroScope_329_ = lean_ctor_get(v_a_315_, 2);
lean_inc(v_currMacroScope_329_);
v_ref_330_ = lean_ctor_get(v_a_315_, 5);
lean_inc(v_ref_330_);
lean_dec_ref(v_a_315_);
v___x_331_ = 0;
v___x_332_ = l_Lean_SourceInfo_fromRef(v_ref_330_, v___x_331_);
lean_dec(v_ref_330_);
v___x_333_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__10, &l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__10_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__10);
v___x_334_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__12));
v___x_335_ = l_Lean_addMacroScope(v_quotContext_328_, v___x_334_, v_currMacroScope_329_);
v___x_336_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__16));
v___x_337_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_337_, 0, v___x_332_);
lean_ctor_set(v___x_337_, 1, v___x_333_);
lean_ctor_set(v___x_337_, 2, v___x_335_);
lean_ctor_set(v___x_337_, 3, v___x_336_);
v___x_338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_338_, 0, v___x_337_);
lean_ctor_set(v___x_338_, 1, v_a_316_);
return v___x_338_;
}
case 2:
{
lean_object* v_quotContext_339_; lean_object* v_currMacroScope_340_; lean_object* v_ref_341_; uint8_t v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v_quotContext_339_ = lean_ctor_get(v_a_315_, 1);
lean_inc(v_quotContext_339_);
v_currMacroScope_340_ = lean_ctor_get(v_a_315_, 2);
lean_inc(v_currMacroScope_340_);
v_ref_341_ = lean_ctor_get(v_a_315_, 5);
lean_inc(v_ref_341_);
lean_dec_ref(v_a_315_);
v___x_342_ = 0;
v___x_343_ = l_Lean_SourceInfo_fromRef(v_ref_341_, v___x_342_);
lean_dec(v_ref_341_);
v___x_344_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__18, &l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__18_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__18);
v___x_345_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__20));
v___x_346_ = l_Lean_addMacroScope(v_quotContext_339_, v___x_345_, v_currMacroScope_340_);
v___x_347_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__24));
v___x_348_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_348_, 0, v___x_343_);
lean_ctor_set(v___x_348_, 1, v___x_344_);
lean_ctor_set(v___x_348_, 2, v___x_346_);
lean_ctor_set(v___x_348_, 3, v___x_347_);
v___x_349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_349_, 0, v___x_348_);
lean_ctor_set(v___x_349_, 1, v_a_316_);
return v___x_349_;
}
default: 
{
lean_object* v_num_350_; lean_object* v_quotContext_351_; lean_object* v_currMacroScope_352_; lean_object* v_ref_353_; uint8_t v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v_num_350_ = lean_ctor_get(v_x_314_, 0);
lean_inc(v_num_350_);
lean_dec_ref(v_x_314_);
v_quotContext_351_ = lean_ctor_get(v_a_315_, 1);
lean_inc(v_quotContext_351_);
v_currMacroScope_352_ = lean_ctor_get(v_a_315_, 2);
lean_inc(v_currMacroScope_352_);
v_ref_353_ = lean_ctor_get(v_a_315_, 5);
lean_inc(v_ref_353_);
lean_dec_ref(v_a_315_);
v___x_354_ = 0;
v___x_355_ = l_Lean_SourceInfo_fromRef(v_ref_353_, v___x_354_);
lean_dec(v_ref_353_);
v___x_356_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_357_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__26, &l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__26_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__26);
v___x_358_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__28));
v___x_359_ = l_Lean_addMacroScope(v_quotContext_351_, v___x_358_, v_currMacroScope_352_);
v___x_360_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertYear___closed__32));
lean_inc(v___x_355_);
v___x_361_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_361_, 0, v___x_355_);
lean_ctor_set(v___x_361_, 1, v___x_357_);
lean_ctor_set(v___x_361_, 2, v___x_359_);
lean_ctor_set(v___x_361_, 3, v___x_360_);
v___x_362_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_363_ = l_Nat_reprFast(v_num_350_);
v___x_364_ = lean_box(2);
v___x_365_ = l_Lean_Syntax_mkNumLit(v___x_363_, v___x_364_);
lean_inc(v___x_355_);
v___x_366_ = l_Lean_Syntax_node1(v___x_355_, v___x_362_, v___x_365_);
v___x_367_ = l_Lean_Syntax_node2(v___x_355_, v___x_356_, v___x_361_, v___x_366_);
v___x_368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_368_, 0, v___x_367_);
lean_ctor_set(v___x_368_, 1, v_a_316_);
return v___x_368_;
}
}
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__1(void){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_370_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__0));
v___x_371_ = l_String_toRawSubstring_x27(v___x_370_);
return v___x_371_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__9(void){
_start:
{
lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_390_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__8));
v___x_391_ = l_String_toRawSubstring_x27(v___x_390_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZoneName(uint8_t v_x_408_, lean_object* v_a_409_, lean_object* v_a_410_){
_start:
{
if (v_x_408_ == 0)
{
lean_object* v_quotContext_411_; lean_object* v_currMacroScope_412_; lean_object* v_ref_413_; uint8_t v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
v_quotContext_411_ = lean_ctor_get(v_a_409_, 1);
lean_inc(v_quotContext_411_);
v_currMacroScope_412_ = lean_ctor_get(v_a_409_, 2);
lean_inc(v_currMacroScope_412_);
v_ref_413_ = lean_ctor_get(v_a_409_, 5);
lean_inc(v_ref_413_);
lean_dec_ref(v_a_409_);
v___x_414_ = 0;
v___x_415_ = l_Lean_SourceInfo_fromRef(v_ref_413_, v___x_414_);
lean_dec(v_ref_413_);
v___x_416_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__1, &l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__1_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__1);
v___x_417_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__3));
v___x_418_ = l_Lean_addMacroScope(v_quotContext_411_, v___x_417_, v_currMacroScope_412_);
v___x_419_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__7));
v___x_420_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_420_, 0, v___x_415_);
lean_ctor_set(v___x_420_, 1, v___x_416_);
lean_ctor_set(v___x_420_, 2, v___x_418_);
lean_ctor_set(v___x_420_, 3, v___x_419_);
v___x_421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_421_, 0, v___x_420_);
lean_ctor_set(v___x_421_, 1, v_a_410_);
return v___x_421_;
}
else
{
lean_object* v_quotContext_422_; lean_object* v_currMacroScope_423_; lean_object* v_ref_424_; uint8_t v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; 
v_quotContext_422_ = lean_ctor_get(v_a_409_, 1);
lean_inc(v_quotContext_422_);
v_currMacroScope_423_ = lean_ctor_get(v_a_409_, 2);
lean_inc(v_currMacroScope_423_);
v_ref_424_ = lean_ctor_get(v_a_409_, 5);
lean_inc(v_ref_424_);
lean_dec_ref(v_a_409_);
v___x_425_ = 0;
v___x_426_ = l_Lean_SourceInfo_fromRef(v_ref_424_, v___x_425_);
lean_dec(v_ref_424_);
v___x_427_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__9, &l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__9_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__9);
v___x_428_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__10));
v___x_429_ = l_Lean_addMacroScope(v_quotContext_422_, v___x_428_, v_currMacroScope_423_);
v___x_430_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertZoneName___closed__14));
v___x_431_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_431_, 0, v___x_426_);
lean_ctor_set(v___x_431_, 1, v___x_427_);
lean_ctor_set(v___x_431_, 2, v___x_429_);
lean_ctor_set(v___x_431_, 3, v___x_430_);
v___x_432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_432_, 0, v___x_431_);
lean_ctor_set(v___x_432_, 1, v_a_410_);
return v___x_432_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZoneName___boxed(lean_object* v_x_433_, lean_object* v_a_434_, lean_object* v_a_435_){
_start:
{
uint8_t v_x_2693__boxed_436_; lean_object* v_res_437_; 
v_x_2693__boxed_436_ = lean_unbox(v_x_433_);
v_res_437_ = l___private_Std_Time_Notation_0__Std_Time_convertZoneName(v_x_2693__boxed_436_, v_a_434_, v_a_435_);
return v_res_437_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__1(void){
_start:
{
lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_439_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__0));
v___x_440_ = l_String_toRawSubstring_x27(v___x_439_);
return v___x_440_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__10(void){
_start:
{
lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_460_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__9));
v___x_461_ = l_String_toRawSubstring_x27(v___x_460_);
return v___x_461_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__18(void){
_start:
{
lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_480_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__17));
v___x_481_ = l_String_toRawSubstring_x27(v___x_480_);
return v___x_481_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__26(void){
_start:
{
lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_500_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__25));
v___x_501_ = l_String_toRawSubstring_x27(v___x_500_);
return v___x_501_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__34(void){
_start:
{
lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_520_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__33));
v___x_521_ = l_String_toRawSubstring_x27(v___x_520_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetX(uint8_t v_x_539_, lean_object* v_a_540_, lean_object* v_a_541_){
_start:
{
switch(v_x_539_)
{
case 0:
{
lean_object* v_quotContext_542_; lean_object* v_currMacroScope_543_; lean_object* v_ref_544_; uint8_t v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
v_quotContext_542_ = lean_ctor_get(v_a_540_, 1);
lean_inc(v_quotContext_542_);
v_currMacroScope_543_ = lean_ctor_get(v_a_540_, 2);
lean_inc(v_currMacroScope_543_);
v_ref_544_ = lean_ctor_get(v_a_540_, 5);
lean_inc(v_ref_544_);
lean_dec_ref(v_a_540_);
v___x_545_ = 0;
v___x_546_ = l_Lean_SourceInfo_fromRef(v_ref_544_, v___x_545_);
lean_dec(v_ref_544_);
v___x_547_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__1, &l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__1_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__1);
v___x_548_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__4));
v___x_549_ = l_Lean_addMacroScope(v_quotContext_542_, v___x_548_, v_currMacroScope_543_);
v___x_550_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__8));
v___x_551_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_551_, 0, v___x_546_);
lean_ctor_set(v___x_551_, 1, v___x_547_);
lean_ctor_set(v___x_551_, 2, v___x_549_);
lean_ctor_set(v___x_551_, 3, v___x_550_);
v___x_552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_552_, 0, v___x_551_);
lean_ctor_set(v___x_552_, 1, v_a_541_);
return v___x_552_;
}
case 1:
{
lean_object* v_quotContext_553_; lean_object* v_currMacroScope_554_; lean_object* v_ref_555_; uint8_t v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
v_quotContext_553_ = lean_ctor_get(v_a_540_, 1);
lean_inc(v_quotContext_553_);
v_currMacroScope_554_ = lean_ctor_get(v_a_540_, 2);
lean_inc(v_currMacroScope_554_);
v_ref_555_ = lean_ctor_get(v_a_540_, 5);
lean_inc(v_ref_555_);
lean_dec_ref(v_a_540_);
v___x_556_ = 0;
v___x_557_ = l_Lean_SourceInfo_fromRef(v_ref_555_, v___x_556_);
lean_dec(v_ref_555_);
v___x_558_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__10, &l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__10_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__10);
v___x_559_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__12));
v___x_560_ = l_Lean_addMacroScope(v_quotContext_553_, v___x_559_, v_currMacroScope_554_);
v___x_561_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__16));
v___x_562_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_562_, 0, v___x_557_);
lean_ctor_set(v___x_562_, 1, v___x_558_);
lean_ctor_set(v___x_562_, 2, v___x_560_);
lean_ctor_set(v___x_562_, 3, v___x_561_);
v___x_563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_563_, 0, v___x_562_);
lean_ctor_set(v___x_563_, 1, v_a_541_);
return v___x_563_;
}
case 2:
{
lean_object* v_quotContext_564_; lean_object* v_currMacroScope_565_; lean_object* v_ref_566_; uint8_t v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
v_quotContext_564_ = lean_ctor_get(v_a_540_, 1);
lean_inc(v_quotContext_564_);
v_currMacroScope_565_ = lean_ctor_get(v_a_540_, 2);
lean_inc(v_currMacroScope_565_);
v_ref_566_ = lean_ctor_get(v_a_540_, 5);
lean_inc(v_ref_566_);
lean_dec_ref(v_a_540_);
v___x_567_ = 0;
v___x_568_ = l_Lean_SourceInfo_fromRef(v_ref_566_, v___x_567_);
lean_dec(v_ref_566_);
v___x_569_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__18, &l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__18_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__18);
v___x_570_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__20));
v___x_571_ = l_Lean_addMacroScope(v_quotContext_564_, v___x_570_, v_currMacroScope_565_);
v___x_572_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__24));
v___x_573_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_573_, 0, v___x_568_);
lean_ctor_set(v___x_573_, 1, v___x_569_);
lean_ctor_set(v___x_573_, 2, v___x_571_);
lean_ctor_set(v___x_573_, 3, v___x_572_);
v___x_574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_574_, 0, v___x_573_);
lean_ctor_set(v___x_574_, 1, v_a_541_);
return v___x_574_;
}
case 3:
{
lean_object* v_quotContext_575_; lean_object* v_currMacroScope_576_; lean_object* v_ref_577_; uint8_t v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v_quotContext_575_ = lean_ctor_get(v_a_540_, 1);
lean_inc(v_quotContext_575_);
v_currMacroScope_576_ = lean_ctor_get(v_a_540_, 2);
lean_inc(v_currMacroScope_576_);
v_ref_577_ = lean_ctor_get(v_a_540_, 5);
lean_inc(v_ref_577_);
lean_dec_ref(v_a_540_);
v___x_578_ = 0;
v___x_579_ = l_Lean_SourceInfo_fromRef(v_ref_577_, v___x_578_);
lean_dec(v_ref_577_);
v___x_580_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__26, &l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__26_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__26);
v___x_581_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__28));
v___x_582_ = l_Lean_addMacroScope(v_quotContext_575_, v___x_581_, v_currMacroScope_576_);
v___x_583_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__32));
v___x_584_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_584_, 0, v___x_579_);
lean_ctor_set(v___x_584_, 1, v___x_580_);
lean_ctor_set(v___x_584_, 2, v___x_582_);
lean_ctor_set(v___x_584_, 3, v___x_583_);
v___x_585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_585_, 0, v___x_584_);
lean_ctor_set(v___x_585_, 1, v_a_541_);
return v___x_585_;
}
default: 
{
lean_object* v_quotContext_586_; lean_object* v_currMacroScope_587_; lean_object* v_ref_588_; uint8_t v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; 
v_quotContext_586_ = lean_ctor_get(v_a_540_, 1);
lean_inc(v_quotContext_586_);
v_currMacroScope_587_ = lean_ctor_get(v_a_540_, 2);
lean_inc(v_currMacroScope_587_);
v_ref_588_ = lean_ctor_get(v_a_540_, 5);
lean_inc(v_ref_588_);
lean_dec_ref(v_a_540_);
v___x_589_ = 0;
v___x_590_ = l_Lean_SourceInfo_fromRef(v_ref_588_, v___x_589_);
lean_dec(v_ref_588_);
v___x_591_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__34, &l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__34_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__34);
v___x_592_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__36));
v___x_593_ = l_Lean_addMacroScope(v_quotContext_586_, v___x_592_, v_currMacroScope_587_);
v___x_594_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___closed__40));
v___x_595_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_595_, 0, v___x_590_);
lean_ctor_set(v___x_595_, 1, v___x_591_);
lean_ctor_set(v___x_595_, 2, v___x_593_);
lean_ctor_set(v___x_595_, 3, v___x_594_);
v___x_596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_596_, 0, v___x_595_);
lean_ctor_set(v___x_596_, 1, v_a_541_);
return v___x_596_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetX___boxed(lean_object* v_x_597_, lean_object* v_a_598_, lean_object* v_a_599_){
_start:
{
uint8_t v_x_6718__boxed_600_; lean_object* v_res_601_; 
v_x_6718__boxed_600_ = lean_unbox(v_x_597_);
v_res_601_ = l___private_Std_Time_Notation_0__Std_Time_convertOffsetX(v_x_6718__boxed_600_, v_a_598_, v_a_599_);
return v_res_601_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__1(void){
_start:
{
lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_603_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__0));
v___x_604_ = l_String_toRawSubstring_x27(v___x_603_);
return v___x_604_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__9(void){
_start:
{
lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_623_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__8));
v___x_624_ = l_String_toRawSubstring_x27(v___x_623_);
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetO(uint8_t v_x_641_, lean_object* v_a_642_, lean_object* v_a_643_){
_start:
{
if (v_x_641_ == 0)
{
lean_object* v_quotContext_644_; lean_object* v_currMacroScope_645_; lean_object* v_ref_646_; uint8_t v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
v_quotContext_644_ = lean_ctor_get(v_a_642_, 1);
lean_inc(v_quotContext_644_);
v_currMacroScope_645_ = lean_ctor_get(v_a_642_, 2);
lean_inc(v_currMacroScope_645_);
v_ref_646_ = lean_ctor_get(v_a_642_, 5);
lean_inc(v_ref_646_);
lean_dec_ref(v_a_642_);
v___x_647_ = 0;
v___x_648_ = l_Lean_SourceInfo_fromRef(v_ref_646_, v___x_647_);
lean_dec(v_ref_646_);
v___x_649_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__1, &l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__1_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__1);
v___x_650_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__3));
v___x_651_ = l_Lean_addMacroScope(v_quotContext_644_, v___x_650_, v_currMacroScope_645_);
v___x_652_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__7));
v___x_653_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_653_, 0, v___x_648_);
lean_ctor_set(v___x_653_, 1, v___x_649_);
lean_ctor_set(v___x_653_, 2, v___x_651_);
lean_ctor_set(v___x_653_, 3, v___x_652_);
v___x_654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_654_, 0, v___x_653_);
lean_ctor_set(v___x_654_, 1, v_a_643_);
return v___x_654_;
}
else
{
lean_object* v_quotContext_655_; lean_object* v_currMacroScope_656_; lean_object* v_ref_657_; uint8_t v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
v_quotContext_655_ = lean_ctor_get(v_a_642_, 1);
lean_inc(v_quotContext_655_);
v_currMacroScope_656_ = lean_ctor_get(v_a_642_, 2);
lean_inc(v_currMacroScope_656_);
v_ref_657_ = lean_ctor_get(v_a_642_, 5);
lean_inc(v_ref_657_);
lean_dec_ref(v_a_642_);
v___x_658_ = 0;
v___x_659_ = l_Lean_SourceInfo_fromRef(v_ref_657_, v___x_658_);
lean_dec(v_ref_657_);
v___x_660_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__9, &l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__9_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__9);
v___x_661_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__10));
v___x_662_ = l_Lean_addMacroScope(v_quotContext_655_, v___x_661_, v_currMacroScope_656_);
v___x_663_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___closed__14));
v___x_664_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_664_, 0, v___x_659_);
lean_ctor_set(v___x_664_, 1, v___x_660_);
lean_ctor_set(v___x_664_, 2, v___x_662_);
lean_ctor_set(v___x_664_, 3, v___x_663_);
v___x_665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_665_, 0, v___x_664_);
lean_ctor_set(v___x_665_, 1, v_a_643_);
return v___x_665_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetO___boxed(lean_object* v_x_666_, lean_object* v_a_667_, lean_object* v_a_668_){
_start:
{
uint8_t v_x_2693__boxed_669_; lean_object* v_res_670_; 
v_x_2693__boxed_669_ = lean_unbox(v_x_666_);
v_res_670_ = l___private_Std_Time_Notation_0__Std_Time_convertOffsetO(v_x_2693__boxed_669_, v_a_667_, v_a_668_);
return v_res_670_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__1(void){
_start:
{
lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_672_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__0));
v___x_673_ = l_String_toRawSubstring_x27(v___x_672_);
return v___x_673_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__9(void){
_start:
{
lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_692_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__8));
v___x_693_ = l_String_toRawSubstring_x27(v___x_692_);
return v___x_693_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__16(void){
_start:
{
lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_711_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__15));
v___x_712_ = l_String_toRawSubstring_x27(v___x_711_);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ(uint8_t v_x_729_, lean_object* v_a_730_, lean_object* v_a_731_){
_start:
{
switch(v_x_729_)
{
case 0:
{
lean_object* v_quotContext_732_; lean_object* v_currMacroScope_733_; lean_object* v_ref_734_; uint8_t v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; 
v_quotContext_732_ = lean_ctor_get(v_a_730_, 1);
lean_inc(v_quotContext_732_);
v_currMacroScope_733_ = lean_ctor_get(v_a_730_, 2);
lean_inc(v_currMacroScope_733_);
v_ref_734_ = lean_ctor_get(v_a_730_, 5);
lean_inc(v_ref_734_);
lean_dec_ref(v_a_730_);
v___x_735_ = 0;
v___x_736_ = l_Lean_SourceInfo_fromRef(v_ref_734_, v___x_735_);
lean_dec(v_ref_734_);
v___x_737_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__1, &l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__1_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__1);
v___x_738_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__3));
v___x_739_ = l_Lean_addMacroScope(v_quotContext_732_, v___x_738_, v_currMacroScope_733_);
v___x_740_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__7));
v___x_741_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_741_, 0, v___x_736_);
lean_ctor_set(v___x_741_, 1, v___x_737_);
lean_ctor_set(v___x_741_, 2, v___x_739_);
lean_ctor_set(v___x_741_, 3, v___x_740_);
v___x_742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_742_, 0, v___x_741_);
lean_ctor_set(v___x_742_, 1, v_a_731_);
return v___x_742_;
}
case 1:
{
lean_object* v_quotContext_743_; lean_object* v_currMacroScope_744_; lean_object* v_ref_745_; uint8_t v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
v_quotContext_743_ = lean_ctor_get(v_a_730_, 1);
lean_inc(v_quotContext_743_);
v_currMacroScope_744_ = lean_ctor_get(v_a_730_, 2);
lean_inc(v_currMacroScope_744_);
v_ref_745_ = lean_ctor_get(v_a_730_, 5);
lean_inc(v_ref_745_);
lean_dec_ref(v_a_730_);
v___x_746_ = 0;
v___x_747_ = l_Lean_SourceInfo_fromRef(v_ref_745_, v___x_746_);
lean_dec(v_ref_745_);
v___x_748_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__9, &l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__9_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__9);
v___x_749_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__10));
v___x_750_ = l_Lean_addMacroScope(v_quotContext_743_, v___x_749_, v_currMacroScope_744_);
v___x_751_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__14));
v___x_752_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_752_, 0, v___x_747_);
lean_ctor_set(v___x_752_, 1, v___x_748_);
lean_ctor_set(v___x_752_, 2, v___x_750_);
lean_ctor_set(v___x_752_, 3, v___x_751_);
v___x_753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_753_, 0, v___x_752_);
lean_ctor_set(v___x_753_, 1, v_a_731_);
return v___x_753_;
}
default: 
{
lean_object* v_quotContext_754_; lean_object* v_currMacroScope_755_; lean_object* v_ref_756_; uint8_t v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; 
v_quotContext_754_ = lean_ctor_get(v_a_730_, 1);
lean_inc(v_quotContext_754_);
v_currMacroScope_755_ = lean_ctor_get(v_a_730_, 2);
lean_inc(v_currMacroScope_755_);
v_ref_756_ = lean_ctor_get(v_a_730_, 5);
lean_inc(v_ref_756_);
lean_dec_ref(v_a_730_);
v___x_757_ = 0;
v___x_758_ = l_Lean_SourceInfo_fromRef(v_ref_756_, v___x_757_);
lean_dec(v_ref_756_);
v___x_759_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__16, &l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__16_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__16);
v___x_760_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__17));
v___x_761_ = l_Lean_addMacroScope(v_quotContext_754_, v___x_760_, v_currMacroScope_755_);
v___x_762_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___closed__21));
v___x_763_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_763_, 0, v___x_758_);
lean_ctor_set(v___x_763_, 1, v___x_759_);
lean_ctor_set(v___x_763_, 2, v___x_761_);
lean_ctor_set(v___x_763_, 3, v___x_762_);
v___x_764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_764_, 0, v___x_763_);
lean_ctor_set(v___x_764_, 1, v_a_731_);
return v___x_764_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ___boxed(lean_object* v_x_765_, lean_object* v_a_766_, lean_object* v_a_767_){
_start:
{
uint8_t v_x_4033__boxed_768_; lean_object* v_res_769_; 
v_x_4033__boxed_768_ = lean_unbox(v_x_765_);
v_res_769_ = l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ(v_x_4033__boxed_768_, v_a_766_, v_a_767_);
return v_res_769_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__1(void){
_start:
{
lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_771_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__0));
v___x_772_ = l_String_toRawSubstring_x27(v___x_771_);
return v___x_772_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__10(void){
_start:
{
lean_object* v___x_792_; lean_object* v___x_793_; 
v___x_792_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__9));
v___x_793_ = l_String_toRawSubstring_x27(v___x_792_);
return v___x_793_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__18(void){
_start:
{
lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_812_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__17));
v___x_813_ = l_String_toRawSubstring_x27(v___x_812_);
return v___x_813_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__26(void){
_start:
{
lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_832_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__25));
v___x_833_ = l_String_toRawSubstring_x27(v___x_832_);
return v___x_833_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__34(void){
_start:
{
lean_object* v___x_852_; lean_object* v___x_853_; 
v___x_852_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__33));
v___x_853_ = l_String_toRawSubstring_x27(v___x_852_);
return v___x_853_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49(void){
_start:
{
lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_888_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__48));
v___x_889_ = l_String_toRawSubstring_x27(v___x_888_);
return v___x_889_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__70(void){
_start:
{
lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_938_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__69));
v___x_939_ = l_String_toRawSubstring_x27(v___x_938_);
return v___x_939_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__74(void){
_start:
{
lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_944_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__73));
v___x_945_ = l_String_toRawSubstring_x27(v___x_944_);
return v___x_945_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__77(void){
_start:
{
lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_949_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__76));
v___x_950_ = l_String_toRawSubstring_x27(v___x_949_);
return v___x_950_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__85(void){
_start:
{
lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_969_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__84));
v___x_970_ = l_String_toRawSubstring_x27(v___x_969_);
return v___x_970_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__93(void){
_start:
{
lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_989_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__92));
v___x_990_ = l_String_toRawSubstring_x27(v___x_989_);
return v___x_990_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__101(void){
_start:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1009_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__100));
v___x_1010_ = l_String_toRawSubstring_x27(v___x_1009_);
return v___x_1010_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__109(void){
_start:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1029_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__108));
v___x_1030_ = l_String_toRawSubstring_x27(v___x_1029_);
return v___x_1030_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__117(void){
_start:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1049_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__116));
v___x_1050_ = l_String_toRawSubstring_x27(v___x_1049_);
return v___x_1050_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__125(void){
_start:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1069_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__124));
v___x_1070_ = l_String_toRawSubstring_x27(v___x_1069_);
return v___x_1070_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__133(void){
_start:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1089_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__132));
v___x_1090_ = l_String_toRawSubstring_x27(v___x_1089_);
return v___x_1090_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__141(void){
_start:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; 
v___x_1109_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__140));
v___x_1110_ = l_String_toRawSubstring_x27(v___x_1109_);
return v___x_1110_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__149(void){
_start:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1129_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__148));
v___x_1130_ = l_String_toRawSubstring_x27(v___x_1129_);
return v___x_1130_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__157(void){
_start:
{
lean_object* v___x_1149_; lean_object* v___x_1150_; 
v___x_1149_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__156));
v___x_1150_ = l_String_toRawSubstring_x27(v___x_1149_);
return v___x_1150_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__165(void){
_start:
{
lean_object* v___x_1169_; lean_object* v___x_1170_; 
v___x_1169_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__164));
v___x_1170_ = l_String_toRawSubstring_x27(v___x_1169_);
return v___x_1170_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__173(void){
_start:
{
lean_object* v___x_1189_; lean_object* v___x_1190_; 
v___x_1189_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__172));
v___x_1190_ = l_String_toRawSubstring_x27(v___x_1189_);
return v___x_1190_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__181(void){
_start:
{
lean_object* v___x_1209_; lean_object* v___x_1210_; 
v___x_1209_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__180));
v___x_1210_ = l_String_toRawSubstring_x27(v___x_1209_);
return v___x_1210_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__189(void){
_start:
{
lean_object* v___x_1229_; lean_object* v___x_1230_; 
v___x_1229_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__188));
v___x_1230_ = l_String_toRawSubstring_x27(v___x_1229_);
return v___x_1230_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__197(void){
_start:
{
lean_object* v___x_1249_; lean_object* v___x_1250_; 
v___x_1249_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__196));
v___x_1250_ = l_String_toRawSubstring_x27(v___x_1249_);
return v___x_1250_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__205(void){
_start:
{
lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1269_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__204));
v___x_1270_ = l_String_toRawSubstring_x27(v___x_1269_);
return v___x_1270_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__213(void){
_start:
{
lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1289_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__212));
v___x_1290_ = l_String_toRawSubstring_x27(v___x_1289_);
return v___x_1290_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__221(void){
_start:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; 
v___x_1309_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__220));
v___x_1310_ = l_String_toRawSubstring_x27(v___x_1309_);
return v___x_1310_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__229(void){
_start:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; 
v___x_1329_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__228));
v___x_1330_ = l_String_toRawSubstring_x27(v___x_1329_);
return v___x_1330_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__237(void){
_start:
{
lean_object* v___x_1349_; lean_object* v___x_1350_; 
v___x_1349_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__236));
v___x_1350_ = l_String_toRawSubstring_x27(v___x_1349_);
return v___x_1350_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__245(void){
_start:
{
lean_object* v___x_1369_; lean_object* v___x_1370_; 
v___x_1369_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__244));
v___x_1370_ = l_String_toRawSubstring_x27(v___x_1369_);
return v___x_1370_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__253(void){
_start:
{
lean_object* v___x_1389_; lean_object* v___x_1390_; 
v___x_1389_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__252));
v___x_1390_ = l_String_toRawSubstring_x27(v___x_1389_);
return v___x_1390_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__261(void){
_start:
{
lean_object* v___x_1409_; lean_object* v___x_1410_; 
v___x_1409_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__260));
v___x_1410_ = l_String_toRawSubstring_x27(v___x_1409_);
return v___x_1410_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier(lean_object* v_x_1428_, lean_object* v_a_1429_, lean_object* v_a_1430_){
_start:
{
switch(lean_obj_tag(v_x_1428_))
{
case 0:
{
uint8_t v_presentation_1431_; lean_object* v___x_1432_; lean_object* v_a_1433_; lean_object* v_a_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1455_; 
v_presentation_1431_ = lean_ctor_get_uint8(v_x_1428_, 0);
lean_dec_ref(v_x_1428_);
lean_inc_ref(v_a_1429_);
v___x_1432_ = l___private_Std_Time_Notation_0__Std_Time_convertText(v_presentation_1431_, v_a_1429_, v_a_1430_);
v_a_1433_ = lean_ctor_get(v___x_1432_, 0);
v_a_1434_ = lean_ctor_get(v___x_1432_, 1);
v_isSharedCheck_1455_ = !lean_is_exclusive(v___x_1432_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1436_ = v___x_1432_;
v_isShared_1437_ = v_isSharedCheck_1455_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_a_1434_);
lean_inc(v_a_1433_);
lean_dec(v___x_1432_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1455_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v_quotContext_1438_; lean_object* v_currMacroScope_1439_; lean_object* v_ref_1440_; uint8_t v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1453_; 
v_quotContext_1438_ = lean_ctor_get(v_a_1429_, 1);
lean_inc(v_quotContext_1438_);
v_currMacroScope_1439_ = lean_ctor_get(v_a_1429_, 2);
lean_inc(v_currMacroScope_1439_);
v_ref_1440_ = lean_ctor_get(v_a_1429_, 5);
lean_inc(v_ref_1440_);
lean_dec_ref(v_a_1429_);
v___x_1441_ = 0;
v___x_1442_ = l_Lean_SourceInfo_fromRef(v_ref_1440_, v___x_1441_);
lean_dec(v_ref_1440_);
v___x_1443_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_1444_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__1, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__1_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__1);
v___x_1445_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__4));
v___x_1446_ = l_Lean_addMacroScope(v_quotContext_1438_, v___x_1445_, v_currMacroScope_1439_);
v___x_1447_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__8));
lean_inc(v___x_1442_);
v___x_1448_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1448_, 0, v___x_1442_);
lean_ctor_set(v___x_1448_, 1, v___x_1444_);
lean_ctor_set(v___x_1448_, 2, v___x_1446_);
lean_ctor_set(v___x_1448_, 3, v___x_1447_);
v___x_1449_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
lean_inc(v___x_1442_);
v___x_1450_ = l_Lean_Syntax_node1(v___x_1442_, v___x_1449_, v_a_1433_);
v___x_1451_ = l_Lean_Syntax_node2(v___x_1442_, v___x_1443_, v___x_1448_, v___x_1450_);
if (v_isShared_1437_ == 0)
{
lean_ctor_set(v___x_1436_, 0, v___x_1451_);
v___x_1453_ = v___x_1436_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v___x_1451_);
lean_ctor_set(v_reuseFailAlloc_1454_, 1, v_a_1434_);
v___x_1453_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
return v___x_1453_;
}
}
}
case 1:
{
lean_object* v_presentation_1456_; lean_object* v___x_1457_; lean_object* v_a_1458_; lean_object* v_a_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1480_; 
v_presentation_1456_ = lean_ctor_get(v_x_1428_, 0);
lean_inc(v_presentation_1456_);
lean_dec_ref(v_x_1428_);
lean_inc_ref(v_a_1429_);
v___x_1457_ = l___private_Std_Time_Notation_0__Std_Time_convertYear(v_presentation_1456_, v_a_1429_, v_a_1430_);
v_a_1458_ = lean_ctor_get(v___x_1457_, 0);
v_a_1459_ = lean_ctor_get(v___x_1457_, 1);
v_isSharedCheck_1480_ = !lean_is_exclusive(v___x_1457_);
if (v_isSharedCheck_1480_ == 0)
{
v___x_1461_ = v___x_1457_;
v_isShared_1462_ = v_isSharedCheck_1480_;
goto v_resetjp_1460_;
}
else
{
lean_inc(v_a_1459_);
lean_inc(v_a_1458_);
lean_dec(v___x_1457_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1480_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
lean_object* v_quotContext_1463_; lean_object* v_currMacroScope_1464_; lean_object* v_ref_1465_; uint8_t v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1478_; 
v_quotContext_1463_ = lean_ctor_get(v_a_1429_, 1);
lean_inc(v_quotContext_1463_);
v_currMacroScope_1464_ = lean_ctor_get(v_a_1429_, 2);
lean_inc(v_currMacroScope_1464_);
v_ref_1465_ = lean_ctor_get(v_a_1429_, 5);
lean_inc(v_ref_1465_);
lean_dec_ref(v_a_1429_);
v___x_1466_ = 0;
v___x_1467_ = l_Lean_SourceInfo_fromRef(v_ref_1465_, v___x_1466_);
lean_dec(v_ref_1465_);
v___x_1468_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_1469_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__10, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__10_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__10);
v___x_1470_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__12));
v___x_1471_ = l_Lean_addMacroScope(v_quotContext_1463_, v___x_1470_, v_currMacroScope_1464_);
v___x_1472_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__16));
lean_inc(v___x_1467_);
v___x_1473_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1473_, 0, v___x_1467_);
lean_ctor_set(v___x_1473_, 1, v___x_1469_);
lean_ctor_set(v___x_1473_, 2, v___x_1471_);
lean_ctor_set(v___x_1473_, 3, v___x_1472_);
v___x_1474_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
lean_inc(v___x_1467_);
v___x_1475_ = l_Lean_Syntax_node1(v___x_1467_, v___x_1474_, v_a_1458_);
v___x_1476_ = l_Lean_Syntax_node2(v___x_1467_, v___x_1468_, v___x_1473_, v___x_1475_);
if (v_isShared_1462_ == 0)
{
lean_ctor_set(v___x_1461_, 0, v___x_1476_);
v___x_1478_ = v___x_1461_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v___x_1476_);
lean_ctor_set(v_reuseFailAlloc_1479_, 1, v_a_1459_);
v___x_1478_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
return v___x_1478_;
}
}
}
case 2:
{
lean_object* v_presentation_1481_; lean_object* v___x_1482_; lean_object* v_a_1483_; lean_object* v_a_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1505_; 
v_presentation_1481_ = lean_ctor_get(v_x_1428_, 0);
lean_inc(v_presentation_1481_);
lean_dec_ref(v_x_1428_);
lean_inc_ref(v_a_1429_);
v___x_1482_ = l___private_Std_Time_Notation_0__Std_Time_convertYear(v_presentation_1481_, v_a_1429_, v_a_1430_);
v_a_1483_ = lean_ctor_get(v___x_1482_, 0);
v_a_1484_ = lean_ctor_get(v___x_1482_, 1);
v_isSharedCheck_1505_ = !lean_is_exclusive(v___x_1482_);
if (v_isSharedCheck_1505_ == 0)
{
v___x_1486_ = v___x_1482_;
v_isShared_1487_ = v_isSharedCheck_1505_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_a_1484_);
lean_inc(v_a_1483_);
lean_dec(v___x_1482_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1505_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
lean_object* v_quotContext_1488_; lean_object* v_currMacroScope_1489_; lean_object* v_ref_1490_; uint8_t v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1503_; 
v_quotContext_1488_ = lean_ctor_get(v_a_1429_, 1);
lean_inc(v_quotContext_1488_);
v_currMacroScope_1489_ = lean_ctor_get(v_a_1429_, 2);
lean_inc(v_currMacroScope_1489_);
v_ref_1490_ = lean_ctor_get(v_a_1429_, 5);
lean_inc(v_ref_1490_);
lean_dec_ref(v_a_1429_);
v___x_1491_ = 0;
v___x_1492_ = l_Lean_SourceInfo_fromRef(v_ref_1490_, v___x_1491_);
lean_dec(v_ref_1490_);
v___x_1493_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_1494_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__18, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__18_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__18);
v___x_1495_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__20));
v___x_1496_ = l_Lean_addMacroScope(v_quotContext_1488_, v___x_1495_, v_currMacroScope_1489_);
v___x_1497_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__24));
lean_inc(v___x_1492_);
v___x_1498_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1498_, 0, v___x_1492_);
lean_ctor_set(v___x_1498_, 1, v___x_1494_);
lean_ctor_set(v___x_1498_, 2, v___x_1496_);
lean_ctor_set(v___x_1498_, 3, v___x_1497_);
v___x_1499_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
lean_inc(v___x_1492_);
v___x_1500_ = l_Lean_Syntax_node1(v___x_1492_, v___x_1499_, v_a_1483_);
v___x_1501_ = l_Lean_Syntax_node2(v___x_1492_, v___x_1493_, v___x_1498_, v___x_1500_);
if (v_isShared_1487_ == 0)
{
lean_ctor_set(v___x_1486_, 0, v___x_1501_);
v___x_1503_ = v___x_1486_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v___x_1501_);
lean_ctor_set(v_reuseFailAlloc_1504_, 1, v_a_1484_);
v___x_1503_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
return v___x_1503_;
}
}
}
case 3:
{
lean_object* v_presentation_1506_; lean_object* v___x_1507_; lean_object* v_a_1508_; lean_object* v_a_1509_; lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1530_; 
v_presentation_1506_ = lean_ctor_get(v_x_1428_, 0);
lean_inc(v_presentation_1506_);
lean_dec_ref(v_x_1428_);
lean_inc_ref(v_a_1429_);
v___x_1507_ = l___private_Std_Time_Notation_0__Std_Time_convertNumber(v_presentation_1506_, v_a_1429_, v_a_1430_);
v_a_1508_ = lean_ctor_get(v___x_1507_, 0);
v_a_1509_ = lean_ctor_get(v___x_1507_, 1);
v_isSharedCheck_1530_ = !lean_is_exclusive(v___x_1507_);
if (v_isSharedCheck_1530_ == 0)
{
v___x_1511_ = v___x_1507_;
v_isShared_1512_ = v_isSharedCheck_1530_;
goto v_resetjp_1510_;
}
else
{
lean_inc(v_a_1509_);
lean_inc(v_a_1508_);
lean_dec(v___x_1507_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1530_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
lean_object* v_quotContext_1513_; lean_object* v_currMacroScope_1514_; lean_object* v_ref_1515_; uint8_t v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1528_; 
v_quotContext_1513_ = lean_ctor_get(v_a_1429_, 1);
lean_inc(v_quotContext_1513_);
v_currMacroScope_1514_ = lean_ctor_get(v_a_1429_, 2);
lean_inc(v_currMacroScope_1514_);
v_ref_1515_ = lean_ctor_get(v_a_1429_, 5);
lean_inc(v_ref_1515_);
lean_dec_ref(v_a_1429_);
v___x_1516_ = 0;
v___x_1517_ = l_Lean_SourceInfo_fromRef(v_ref_1515_, v___x_1516_);
lean_dec(v_ref_1515_);
v___x_1518_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_1519_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__26, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__26_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__26);
v___x_1520_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__28));
v___x_1521_ = l_Lean_addMacroScope(v_quotContext_1513_, v___x_1520_, v_currMacroScope_1514_);
v___x_1522_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__32));
lean_inc(v___x_1517_);
v___x_1523_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1523_, 0, v___x_1517_);
lean_ctor_set(v___x_1523_, 1, v___x_1519_);
lean_ctor_set(v___x_1523_, 2, v___x_1521_);
lean_ctor_set(v___x_1523_, 3, v___x_1522_);
v___x_1524_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
lean_inc(v___x_1517_);
v___x_1525_ = l_Lean_Syntax_node1(v___x_1517_, v___x_1524_, v_a_1508_);
v___x_1526_ = l_Lean_Syntax_node2(v___x_1517_, v___x_1518_, v___x_1523_, v___x_1525_);
if (v_isShared_1512_ == 0)
{
lean_ctor_set(v___x_1511_, 0, v___x_1526_);
v___x_1528_ = v___x_1511_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v___x_1526_);
lean_ctor_set(v_reuseFailAlloc_1529_, 1, v_a_1509_);
v___x_1528_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
return v___x_1528_;
}
}
}
case 4:
{
lean_object* v_presentation_1531_; 
v_presentation_1531_ = lean_ctor_get(v_x_1428_, 0);
lean_inc_ref(v_presentation_1531_);
lean_dec_ref(v_x_1428_);
if (lean_obj_tag(v_presentation_1531_) == 0)
{
lean_object* v_val_1532_; lean_object* v___x_1533_; lean_object* v_a_1534_; lean_object* v_a_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1582_; 
v_val_1532_ = lean_ctor_get(v_presentation_1531_, 0);
lean_inc(v_val_1532_);
lean_dec_ref(v_presentation_1531_);
lean_inc_ref(v_a_1429_);
v___x_1533_ = l___private_Std_Time_Notation_0__Std_Time_convertNumber(v_val_1532_, v_a_1429_, v_a_1430_);
v_a_1534_ = lean_ctor_get(v___x_1533_, 0);
v_a_1535_ = lean_ctor_get(v___x_1533_, 1);
v_isSharedCheck_1582_ = !lean_is_exclusive(v___x_1533_);
if (v_isSharedCheck_1582_ == 0)
{
v___x_1537_ = v___x_1533_;
v_isShared_1538_ = v_isSharedCheck_1582_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_a_1535_);
lean_inc(v_a_1534_);
lean_dec(v___x_1533_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1582_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
lean_object* v_quotContext_1539_; lean_object* v_currMacroScope_1540_; lean_object* v_ref_1541_; uint8_t v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1580_; 
v_quotContext_1539_ = lean_ctor_get(v_a_1429_, 1);
lean_inc(v_quotContext_1539_);
v_currMacroScope_1540_ = lean_ctor_get(v_a_1429_, 2);
lean_inc(v_currMacroScope_1540_);
v_ref_1541_ = lean_ctor_get(v_a_1429_, 5);
lean_inc(v_ref_1541_);
lean_dec_ref(v_a_1429_);
v___x_1542_ = 0;
v___x_1543_ = l_Lean_SourceInfo_fromRef(v_ref_1541_, v___x_1542_);
lean_dec(v_ref_1541_);
v___x_1544_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_1545_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__34, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__34_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__34);
v___x_1546_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__36));
lean_inc(v_currMacroScope_1540_);
lean_inc(v_quotContext_1539_);
v___x_1547_ = l_Lean_addMacroScope(v_quotContext_1539_, v___x_1546_, v_currMacroScope_1540_);
v___x_1548_ = lean_box(0);
v___x_1549_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__40));
lean_inc(v___x_1543_);
v___x_1550_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1550_, 0, v___x_1543_);
lean_ctor_set(v___x_1550_, 1, v___x_1545_);
lean_ctor_set(v___x_1550_, 2, v___x_1547_);
lean_ctor_set(v___x_1550_, 3, v___x_1549_);
v___x_1551_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_1552_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__42));
v___x_1553_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__44));
v___x_1554_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__45));
lean_inc(v___x_1543_);
v___x_1555_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1555_, 0, v___x_1543_);
lean_ctor_set(v___x_1555_, 1, v___x_1554_);
v___x_1556_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__47));
v___x_1557_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49);
v___x_1558_ = lean_box(0);
lean_inc(v_currMacroScope_1540_);
lean_inc(v_quotContext_1539_);
v___x_1559_ = l_Lean_addMacroScope(v_quotContext_1539_, v___x_1558_, v_currMacroScope_1540_);
v___x_1560_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__65));
lean_inc(v___x_1543_);
v___x_1561_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1561_, 0, v___x_1543_);
lean_ctor_set(v___x_1561_, 1, v___x_1557_);
lean_ctor_set(v___x_1561_, 2, v___x_1559_);
lean_ctor_set(v___x_1561_, 3, v___x_1560_);
lean_inc(v___x_1543_);
v___x_1562_ = l_Lean_Syntax_node1(v___x_1543_, v___x_1556_, v___x_1561_);
lean_inc(v___x_1543_);
v___x_1563_ = l_Lean_Syntax_node2(v___x_1543_, v___x_1553_, v___x_1555_, v___x_1562_);
v___x_1564_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__67));
v___x_1565_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__68));
lean_inc(v___x_1543_);
v___x_1566_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1566_, 0, v___x_1543_);
lean_ctor_set(v___x_1566_, 1, v___x_1565_);
v___x_1567_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__70, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__70_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__70);
v___x_1568_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__71));
v___x_1569_ = l_Lean_addMacroScope(v_quotContext_1539_, v___x_1568_, v_currMacroScope_1540_);
lean_inc(v___x_1543_);
v___x_1570_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1570_, 0, v___x_1543_);
lean_ctor_set(v___x_1570_, 1, v___x_1567_);
lean_ctor_set(v___x_1570_, 2, v___x_1569_);
lean_ctor_set(v___x_1570_, 3, v___x_1548_);
lean_inc(v___x_1543_);
v___x_1571_ = l_Lean_Syntax_node2(v___x_1543_, v___x_1564_, v___x_1566_, v___x_1570_);
lean_inc(v___x_1543_);
v___x_1572_ = l_Lean_Syntax_node1(v___x_1543_, v___x_1551_, v_a_1534_);
lean_inc(v___x_1543_);
v___x_1573_ = l_Lean_Syntax_node2(v___x_1543_, v___x_1544_, v___x_1571_, v___x_1572_);
v___x_1574_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__72));
lean_inc(v___x_1543_);
v___x_1575_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1575_, 0, v___x_1543_);
lean_ctor_set(v___x_1575_, 1, v___x_1574_);
lean_inc(v___x_1543_);
v___x_1576_ = l_Lean_Syntax_node3(v___x_1543_, v___x_1552_, v___x_1563_, v___x_1573_, v___x_1575_);
lean_inc(v___x_1543_);
v___x_1577_ = l_Lean_Syntax_node1(v___x_1543_, v___x_1551_, v___x_1576_);
v___x_1578_ = l_Lean_Syntax_node2(v___x_1543_, v___x_1544_, v___x_1550_, v___x_1577_);
if (v_isShared_1538_ == 0)
{
lean_ctor_set(v___x_1537_, 0, v___x_1578_);
v___x_1580_ = v___x_1537_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v___x_1578_);
lean_ctor_set(v_reuseFailAlloc_1581_, 1, v_a_1535_);
v___x_1580_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
return v___x_1580_;
}
}
}
else
{
lean_object* v_val_1583_; uint8_t v___x_1584_; lean_object* v___x_1585_; lean_object* v_a_1586_; lean_object* v_a_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1634_; 
v_val_1583_ = lean_ctor_get(v_presentation_1531_, 0);
lean_inc(v_val_1583_);
lean_dec_ref(v_presentation_1531_);
v___x_1584_ = lean_unbox(v_val_1583_);
lean_dec(v_val_1583_);
lean_inc_ref(v_a_1429_);
v___x_1585_ = l___private_Std_Time_Notation_0__Std_Time_convertText(v___x_1584_, v_a_1429_, v_a_1430_);
v_a_1586_ = lean_ctor_get(v___x_1585_, 0);
v_a_1587_ = lean_ctor_get(v___x_1585_, 1);
v_isSharedCheck_1634_ = !lean_is_exclusive(v___x_1585_);
if (v_isSharedCheck_1634_ == 0)
{
v___x_1589_ = v___x_1585_;
v_isShared_1590_ = v_isSharedCheck_1634_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_a_1587_);
lean_inc(v_a_1586_);
lean_dec(v___x_1585_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1634_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
lean_object* v_quotContext_1591_; lean_object* v_currMacroScope_1592_; lean_object* v_ref_1593_; uint8_t v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1632_; 
v_quotContext_1591_ = lean_ctor_get(v_a_1429_, 1);
lean_inc(v_quotContext_1591_);
v_currMacroScope_1592_ = lean_ctor_get(v_a_1429_, 2);
lean_inc(v_currMacroScope_1592_);
v_ref_1593_ = lean_ctor_get(v_a_1429_, 5);
lean_inc(v_ref_1593_);
lean_dec_ref(v_a_1429_);
v___x_1594_ = 0;
v___x_1595_ = l_Lean_SourceInfo_fromRef(v_ref_1593_, v___x_1594_);
lean_dec(v_ref_1593_);
v___x_1596_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_1597_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__34, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__34_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__34);
v___x_1598_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__36));
lean_inc(v_currMacroScope_1592_);
lean_inc(v_quotContext_1591_);
v___x_1599_ = l_Lean_addMacroScope(v_quotContext_1591_, v___x_1598_, v_currMacroScope_1592_);
v___x_1600_ = lean_box(0);
v___x_1601_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__40));
lean_inc(v___x_1595_);
v___x_1602_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1602_, 0, v___x_1595_);
lean_ctor_set(v___x_1602_, 1, v___x_1597_);
lean_ctor_set(v___x_1602_, 2, v___x_1599_);
lean_ctor_set(v___x_1602_, 3, v___x_1601_);
v___x_1603_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_1604_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__42));
v___x_1605_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__44));
v___x_1606_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__45));
lean_inc(v___x_1595_);
v___x_1607_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1607_, 0, v___x_1595_);
lean_ctor_set(v___x_1607_, 1, v___x_1606_);
v___x_1608_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__47));
v___x_1609_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49);
v___x_1610_ = lean_box(0);
lean_inc(v_currMacroScope_1592_);
lean_inc(v_quotContext_1591_);
v___x_1611_ = l_Lean_addMacroScope(v_quotContext_1591_, v___x_1610_, v_currMacroScope_1592_);
v___x_1612_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__65));
lean_inc(v___x_1595_);
v___x_1613_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1613_, 0, v___x_1595_);
lean_ctor_set(v___x_1613_, 1, v___x_1609_);
lean_ctor_set(v___x_1613_, 2, v___x_1611_);
lean_ctor_set(v___x_1613_, 3, v___x_1612_);
lean_inc(v___x_1595_);
v___x_1614_ = l_Lean_Syntax_node1(v___x_1595_, v___x_1608_, v___x_1613_);
lean_inc(v___x_1595_);
v___x_1615_ = l_Lean_Syntax_node2(v___x_1595_, v___x_1605_, v___x_1607_, v___x_1614_);
v___x_1616_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__67));
v___x_1617_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__68));
lean_inc(v___x_1595_);
v___x_1618_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1618_, 0, v___x_1595_);
lean_ctor_set(v___x_1618_, 1, v___x_1617_);
v___x_1619_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__74, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__74_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__74);
v___x_1620_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__75));
v___x_1621_ = l_Lean_addMacroScope(v_quotContext_1591_, v___x_1620_, v_currMacroScope_1592_);
lean_inc(v___x_1595_);
v___x_1622_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1595_);
lean_ctor_set(v___x_1622_, 1, v___x_1619_);
lean_ctor_set(v___x_1622_, 2, v___x_1621_);
lean_ctor_set(v___x_1622_, 3, v___x_1600_);
lean_inc(v___x_1595_);
v___x_1623_ = l_Lean_Syntax_node2(v___x_1595_, v___x_1616_, v___x_1618_, v___x_1622_);
lean_inc(v___x_1595_);
v___x_1624_ = l_Lean_Syntax_node1(v___x_1595_, v___x_1603_, v_a_1586_);
lean_inc(v___x_1595_);
v___x_1625_ = l_Lean_Syntax_node2(v___x_1595_, v___x_1596_, v___x_1623_, v___x_1624_);
v___x_1626_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__72));
lean_inc(v___x_1595_);
v___x_1627_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1627_, 0, v___x_1595_);
lean_ctor_set(v___x_1627_, 1, v___x_1626_);
lean_inc(v___x_1595_);
v___x_1628_ = l_Lean_Syntax_node3(v___x_1595_, v___x_1604_, v___x_1615_, v___x_1625_, v___x_1627_);
lean_inc(v___x_1595_);
v___x_1629_ = l_Lean_Syntax_node1(v___x_1595_, v___x_1603_, v___x_1628_);
v___x_1630_ = l_Lean_Syntax_node2(v___x_1595_, v___x_1596_, v___x_1602_, v___x_1629_);
if (v_isShared_1590_ == 0)
{
lean_ctor_set(v___x_1589_, 0, v___x_1630_);
v___x_1632_ = v___x_1589_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v___x_1630_);
lean_ctor_set(v_reuseFailAlloc_1633_, 1, v_a_1587_);
v___x_1632_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
return v___x_1632_;
}
}
}
}
case 5:
{
lean_object* v_presentation_1635_; lean_object* v___x_1636_; lean_object* v_a_1637_; lean_object* v_a_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1659_; 
v_presentation_1635_ = lean_ctor_get(v_x_1428_, 0);
lean_inc(v_presentation_1635_);
lean_dec_ref(v_x_1428_);
lean_inc_ref(v_a_1429_);
v___x_1636_ = l___private_Std_Time_Notation_0__Std_Time_convertNumber(v_presentation_1635_, v_a_1429_, v_a_1430_);
v_a_1637_ = lean_ctor_get(v___x_1636_, 0);
v_a_1638_ = lean_ctor_get(v___x_1636_, 1);
v_isSharedCheck_1659_ = !lean_is_exclusive(v___x_1636_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1640_ = v___x_1636_;
v_isShared_1641_ = v_isSharedCheck_1659_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_a_1638_);
lean_inc(v_a_1637_);
lean_dec(v___x_1636_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1659_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v_quotContext_1642_; lean_object* v_currMacroScope_1643_; lean_object* v_ref_1644_; uint8_t v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1657_; 
v_quotContext_1642_ = lean_ctor_get(v_a_1429_, 1);
lean_inc(v_quotContext_1642_);
v_currMacroScope_1643_ = lean_ctor_get(v_a_1429_, 2);
lean_inc(v_currMacroScope_1643_);
v_ref_1644_ = lean_ctor_get(v_a_1429_, 5);
lean_inc(v_ref_1644_);
lean_dec_ref(v_a_1429_);
v___x_1645_ = 0;
v___x_1646_ = l_Lean_SourceInfo_fromRef(v_ref_1644_, v___x_1645_);
lean_dec(v_ref_1644_);
v___x_1647_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_1648_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__77, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__77_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__77);
v___x_1649_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__79));
v___x_1650_ = l_Lean_addMacroScope(v_quotContext_1642_, v___x_1649_, v_currMacroScope_1643_);
v___x_1651_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__83));
lean_inc(v___x_1646_);
v___x_1652_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1652_, 0, v___x_1646_);
lean_ctor_set(v___x_1652_, 1, v___x_1648_);
lean_ctor_set(v___x_1652_, 2, v___x_1650_);
lean_ctor_set(v___x_1652_, 3, v___x_1651_);
v___x_1653_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
lean_inc(v___x_1646_);
v___x_1654_ = l_Lean_Syntax_node1(v___x_1646_, v___x_1653_, v_a_1637_);
v___x_1655_ = l_Lean_Syntax_node2(v___x_1646_, v___x_1647_, v___x_1652_, v___x_1654_);
if (v_isShared_1641_ == 0)
{
lean_ctor_set(v___x_1640_, 0, v___x_1655_);
v___x_1657_ = v___x_1640_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v___x_1655_);
lean_ctor_set(v_reuseFailAlloc_1658_, 1, v_a_1638_);
v___x_1657_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
return v___x_1657_;
}
}
}
case 6:
{
lean_object* v_presentation_1660_; 
v_presentation_1660_ = lean_ctor_get(v_x_1428_, 0);
lean_inc_ref(v_presentation_1660_);
lean_dec_ref(v_x_1428_);
if (lean_obj_tag(v_presentation_1660_) == 0)
{
lean_object* v_val_1661_; lean_object* v___x_1662_; lean_object* v_a_1663_; lean_object* v_a_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1711_; 
v_val_1661_ = lean_ctor_get(v_presentation_1660_, 0);
lean_inc(v_val_1661_);
lean_dec_ref(v_presentation_1660_);
lean_inc_ref(v_a_1429_);
v___x_1662_ = l___private_Std_Time_Notation_0__Std_Time_convertNumber(v_val_1661_, v_a_1429_, v_a_1430_);
v_a_1663_ = lean_ctor_get(v___x_1662_, 0);
v_a_1664_ = lean_ctor_get(v___x_1662_, 1);
v_isSharedCheck_1711_ = !lean_is_exclusive(v___x_1662_);
if (v_isSharedCheck_1711_ == 0)
{
v___x_1666_ = v___x_1662_;
v_isShared_1667_ = v_isSharedCheck_1711_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_a_1664_);
lean_inc(v_a_1663_);
lean_dec(v___x_1662_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1711_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v_quotContext_1668_; lean_object* v_currMacroScope_1669_; lean_object* v_ref_1670_; uint8_t v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1709_; 
v_quotContext_1668_ = lean_ctor_get(v_a_1429_, 1);
lean_inc(v_quotContext_1668_);
v_currMacroScope_1669_ = lean_ctor_get(v_a_1429_, 2);
lean_inc(v_currMacroScope_1669_);
v_ref_1670_ = lean_ctor_get(v_a_1429_, 5);
lean_inc(v_ref_1670_);
lean_dec_ref(v_a_1429_);
v___x_1671_ = 0;
v___x_1672_ = l_Lean_SourceInfo_fromRef(v_ref_1670_, v___x_1671_);
lean_dec(v_ref_1670_);
v___x_1673_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_1674_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__85, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__85_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__85);
v___x_1675_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__87));
lean_inc(v_currMacroScope_1669_);
lean_inc(v_quotContext_1668_);
v___x_1676_ = l_Lean_addMacroScope(v_quotContext_1668_, v___x_1675_, v_currMacroScope_1669_);
v___x_1677_ = lean_box(0);
v___x_1678_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__91));
lean_inc(v___x_1672_);
v___x_1679_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1679_, 0, v___x_1672_);
lean_ctor_set(v___x_1679_, 1, v___x_1674_);
lean_ctor_set(v___x_1679_, 2, v___x_1676_);
lean_ctor_set(v___x_1679_, 3, v___x_1678_);
v___x_1680_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_1681_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__42));
v___x_1682_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__44));
v___x_1683_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__45));
lean_inc(v___x_1672_);
v___x_1684_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1684_, 0, v___x_1672_);
lean_ctor_set(v___x_1684_, 1, v___x_1683_);
v___x_1685_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__47));
v___x_1686_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49);
v___x_1687_ = lean_box(0);
lean_inc(v_currMacroScope_1669_);
lean_inc(v_quotContext_1668_);
v___x_1688_ = l_Lean_addMacroScope(v_quotContext_1668_, v___x_1687_, v_currMacroScope_1669_);
v___x_1689_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__65));
lean_inc(v___x_1672_);
v___x_1690_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1690_, 0, v___x_1672_);
lean_ctor_set(v___x_1690_, 1, v___x_1686_);
lean_ctor_set(v___x_1690_, 2, v___x_1688_);
lean_ctor_set(v___x_1690_, 3, v___x_1689_);
lean_inc(v___x_1672_);
v___x_1691_ = l_Lean_Syntax_node1(v___x_1672_, v___x_1685_, v___x_1690_);
lean_inc(v___x_1672_);
v___x_1692_ = l_Lean_Syntax_node2(v___x_1672_, v___x_1682_, v___x_1684_, v___x_1691_);
v___x_1693_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__67));
v___x_1694_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__68));
lean_inc(v___x_1672_);
v___x_1695_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1695_, 0, v___x_1672_);
lean_ctor_set(v___x_1695_, 1, v___x_1694_);
v___x_1696_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__70, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__70_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__70);
v___x_1697_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__71));
v___x_1698_ = l_Lean_addMacroScope(v_quotContext_1668_, v___x_1697_, v_currMacroScope_1669_);
lean_inc(v___x_1672_);
v___x_1699_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1699_, 0, v___x_1672_);
lean_ctor_set(v___x_1699_, 1, v___x_1696_);
lean_ctor_set(v___x_1699_, 2, v___x_1698_);
lean_ctor_set(v___x_1699_, 3, v___x_1677_);
lean_inc(v___x_1672_);
v___x_1700_ = l_Lean_Syntax_node2(v___x_1672_, v___x_1693_, v___x_1695_, v___x_1699_);
lean_inc(v___x_1672_);
v___x_1701_ = l_Lean_Syntax_node1(v___x_1672_, v___x_1680_, v_a_1663_);
lean_inc(v___x_1672_);
v___x_1702_ = l_Lean_Syntax_node2(v___x_1672_, v___x_1673_, v___x_1700_, v___x_1701_);
v___x_1703_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__72));
lean_inc(v___x_1672_);
v___x_1704_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1704_, 0, v___x_1672_);
lean_ctor_set(v___x_1704_, 1, v___x_1703_);
lean_inc(v___x_1672_);
v___x_1705_ = l_Lean_Syntax_node3(v___x_1672_, v___x_1681_, v___x_1692_, v___x_1702_, v___x_1704_);
lean_inc(v___x_1672_);
v___x_1706_ = l_Lean_Syntax_node1(v___x_1672_, v___x_1680_, v___x_1705_);
v___x_1707_ = l_Lean_Syntax_node2(v___x_1672_, v___x_1673_, v___x_1679_, v___x_1706_);
if (v_isShared_1667_ == 0)
{
lean_ctor_set(v___x_1666_, 0, v___x_1707_);
v___x_1709_ = v___x_1666_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v___x_1707_);
lean_ctor_set(v_reuseFailAlloc_1710_, 1, v_a_1664_);
v___x_1709_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
return v___x_1709_;
}
}
}
else
{
lean_object* v_val_1712_; uint8_t v___x_1713_; lean_object* v___x_1714_; lean_object* v_a_1715_; lean_object* v_a_1716_; lean_object* v___x_1718_; uint8_t v_isShared_1719_; uint8_t v_isSharedCheck_1763_; 
v_val_1712_ = lean_ctor_get(v_presentation_1660_, 0);
lean_inc(v_val_1712_);
lean_dec_ref(v_presentation_1660_);
v___x_1713_ = lean_unbox(v_val_1712_);
lean_dec(v_val_1712_);
lean_inc_ref(v_a_1429_);
v___x_1714_ = l___private_Std_Time_Notation_0__Std_Time_convertText(v___x_1713_, v_a_1429_, v_a_1430_);
v_a_1715_ = lean_ctor_get(v___x_1714_, 0);
v_a_1716_ = lean_ctor_get(v___x_1714_, 1);
v_isSharedCheck_1763_ = !lean_is_exclusive(v___x_1714_);
if (v_isSharedCheck_1763_ == 0)
{
v___x_1718_ = v___x_1714_;
v_isShared_1719_ = v_isSharedCheck_1763_;
goto v_resetjp_1717_;
}
else
{
lean_inc(v_a_1716_);
lean_inc(v_a_1715_);
lean_dec(v___x_1714_);
v___x_1718_ = lean_box(0);
v_isShared_1719_ = v_isSharedCheck_1763_;
goto v_resetjp_1717_;
}
v_resetjp_1717_:
{
lean_object* v_quotContext_1720_; lean_object* v_currMacroScope_1721_; lean_object* v_ref_1722_; uint8_t v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1761_; 
v_quotContext_1720_ = lean_ctor_get(v_a_1429_, 1);
lean_inc(v_quotContext_1720_);
v_currMacroScope_1721_ = lean_ctor_get(v_a_1429_, 2);
lean_inc(v_currMacroScope_1721_);
v_ref_1722_ = lean_ctor_get(v_a_1429_, 5);
lean_inc(v_ref_1722_);
lean_dec_ref(v_a_1429_);
v___x_1723_ = 0;
v___x_1724_ = l_Lean_SourceInfo_fromRef(v_ref_1722_, v___x_1723_);
lean_dec(v_ref_1722_);
v___x_1725_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_1726_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__85, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__85_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__85);
v___x_1727_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__87));
lean_inc(v_currMacroScope_1721_);
lean_inc(v_quotContext_1720_);
v___x_1728_ = l_Lean_addMacroScope(v_quotContext_1720_, v___x_1727_, v_currMacroScope_1721_);
v___x_1729_ = lean_box(0);
v___x_1730_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__91));
lean_inc(v___x_1724_);
v___x_1731_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1731_, 0, v___x_1724_);
lean_ctor_set(v___x_1731_, 1, v___x_1726_);
lean_ctor_set(v___x_1731_, 2, v___x_1728_);
lean_ctor_set(v___x_1731_, 3, v___x_1730_);
v___x_1732_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_1733_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__42));
v___x_1734_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__44));
v___x_1735_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__45));
lean_inc(v___x_1724_);
v___x_1736_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1736_, 0, v___x_1724_);
lean_ctor_set(v___x_1736_, 1, v___x_1735_);
v___x_1737_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__47));
v___x_1738_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49);
v___x_1739_ = lean_box(0);
lean_inc(v_currMacroScope_1721_);
lean_inc(v_quotContext_1720_);
v___x_1740_ = l_Lean_addMacroScope(v_quotContext_1720_, v___x_1739_, v_currMacroScope_1721_);
v___x_1741_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__65));
lean_inc(v___x_1724_);
v___x_1742_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1742_, 0, v___x_1724_);
lean_ctor_set(v___x_1742_, 1, v___x_1738_);
lean_ctor_set(v___x_1742_, 2, v___x_1740_);
lean_ctor_set(v___x_1742_, 3, v___x_1741_);
lean_inc(v___x_1724_);
v___x_1743_ = l_Lean_Syntax_node1(v___x_1724_, v___x_1737_, v___x_1742_);
lean_inc(v___x_1724_);
v___x_1744_ = l_Lean_Syntax_node2(v___x_1724_, v___x_1734_, v___x_1736_, v___x_1743_);
v___x_1745_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__67));
v___x_1746_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__68));
lean_inc(v___x_1724_);
v___x_1747_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1747_, 0, v___x_1724_);
lean_ctor_set(v___x_1747_, 1, v___x_1746_);
v___x_1748_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__74, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__74_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__74);
v___x_1749_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__75));
v___x_1750_ = l_Lean_addMacroScope(v_quotContext_1720_, v___x_1749_, v_currMacroScope_1721_);
lean_inc(v___x_1724_);
v___x_1751_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1751_, 0, v___x_1724_);
lean_ctor_set(v___x_1751_, 1, v___x_1748_);
lean_ctor_set(v___x_1751_, 2, v___x_1750_);
lean_ctor_set(v___x_1751_, 3, v___x_1729_);
lean_inc(v___x_1724_);
v___x_1752_ = l_Lean_Syntax_node2(v___x_1724_, v___x_1745_, v___x_1747_, v___x_1751_);
lean_inc(v___x_1724_);
v___x_1753_ = l_Lean_Syntax_node1(v___x_1724_, v___x_1732_, v_a_1715_);
lean_inc(v___x_1724_);
v___x_1754_ = l_Lean_Syntax_node2(v___x_1724_, v___x_1725_, v___x_1752_, v___x_1753_);
v___x_1755_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__72));
lean_inc(v___x_1724_);
v___x_1756_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1756_, 0, v___x_1724_);
lean_ctor_set(v___x_1756_, 1, v___x_1755_);
lean_inc(v___x_1724_);
v___x_1757_ = l_Lean_Syntax_node3(v___x_1724_, v___x_1733_, v___x_1744_, v___x_1754_, v___x_1756_);
lean_inc(v___x_1724_);
v___x_1758_ = l_Lean_Syntax_node1(v___x_1724_, v___x_1732_, v___x_1757_);
v___x_1759_ = l_Lean_Syntax_node2(v___x_1724_, v___x_1725_, v___x_1731_, v___x_1758_);
if (v_isShared_1719_ == 0)
{
lean_ctor_set(v___x_1718_, 0, v___x_1759_);
v___x_1761_ = v___x_1718_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v___x_1759_);
lean_ctor_set(v_reuseFailAlloc_1762_, 1, v_a_1716_);
v___x_1761_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
return v___x_1761_;
}
}
}
}
case 7:
{
lean_object* v_presentation_1764_; lean_object* v___x_1765_; lean_object* v_a_1766_; lean_object* v_a_1767_; lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1788_; 
v_presentation_1764_ = lean_ctor_get(v_x_1428_, 0);
lean_inc(v_presentation_1764_);
lean_dec_ref(v_x_1428_);
lean_inc_ref(v_a_1429_);
v___x_1765_ = l___private_Std_Time_Notation_0__Std_Time_convertNumber(v_presentation_1764_, v_a_1429_, v_a_1430_);
v_a_1766_ = lean_ctor_get(v___x_1765_, 0);
v_a_1767_ = lean_ctor_get(v___x_1765_, 1);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1765_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1769_ = v___x_1765_;
v_isShared_1770_ = v_isSharedCheck_1788_;
goto v_resetjp_1768_;
}
else
{
lean_inc(v_a_1767_);
lean_inc(v_a_1766_);
lean_dec(v___x_1765_);
v___x_1769_ = lean_box(0);
v_isShared_1770_ = v_isSharedCheck_1788_;
goto v_resetjp_1768_;
}
v_resetjp_1768_:
{
lean_object* v_quotContext_1771_; lean_object* v_currMacroScope_1772_; lean_object* v_ref_1773_; uint8_t v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1786_; 
v_quotContext_1771_ = lean_ctor_get(v_a_1429_, 1);
lean_inc(v_quotContext_1771_);
v_currMacroScope_1772_ = lean_ctor_get(v_a_1429_, 2);
lean_inc(v_currMacroScope_1772_);
v_ref_1773_ = lean_ctor_get(v_a_1429_, 5);
lean_inc(v_ref_1773_);
lean_dec_ref(v_a_1429_);
v___x_1774_ = 0;
v___x_1775_ = l_Lean_SourceInfo_fromRef(v_ref_1773_, v___x_1774_);
lean_dec(v_ref_1773_);
v___x_1776_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_1777_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__93, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__93_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__93);
v___x_1778_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__95));
v___x_1779_ = l_Lean_addMacroScope(v_quotContext_1771_, v___x_1778_, v_currMacroScope_1772_);
v___x_1780_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__99));
lean_inc(v___x_1775_);
v___x_1781_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1781_, 0, v___x_1775_);
lean_ctor_set(v___x_1781_, 1, v___x_1777_);
lean_ctor_set(v___x_1781_, 2, v___x_1779_);
lean_ctor_set(v___x_1781_, 3, v___x_1780_);
v___x_1782_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
lean_inc(v___x_1775_);
v___x_1783_ = l_Lean_Syntax_node1(v___x_1775_, v___x_1782_, v_a_1766_);
v___x_1784_ = l_Lean_Syntax_node2(v___x_1775_, v___x_1776_, v___x_1781_, v___x_1783_);
if (v_isShared_1770_ == 0)
{
lean_ctor_set(v___x_1769_, 0, v___x_1784_);
v___x_1786_ = v___x_1769_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v___x_1784_);
lean_ctor_set(v_reuseFailAlloc_1787_, 1, v_a_1767_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
return v___x_1786_;
}
}
}
case 8:
{
lean_object* v_presentation_1789_; lean_object* v___x_1790_; lean_object* v_a_1791_; lean_object* v_a_1792_; lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1813_; 
v_presentation_1789_ = lean_ctor_get(v_x_1428_, 0);
lean_inc(v_presentation_1789_);
lean_dec_ref(v_x_1428_);
lean_inc_ref(v_a_1429_);
v___x_1790_ = l___private_Std_Time_Notation_0__Std_Time_convertNumber(v_presentation_1789_, v_a_1429_, v_a_1430_);
v_a_1791_ = lean_ctor_get(v___x_1790_, 0);
v_a_1792_ = lean_ctor_get(v___x_1790_, 1);
v_isSharedCheck_1813_ = !lean_is_exclusive(v___x_1790_);
if (v_isSharedCheck_1813_ == 0)
{
v___x_1794_ = v___x_1790_;
v_isShared_1795_ = v_isSharedCheck_1813_;
goto v_resetjp_1793_;
}
else
{
lean_inc(v_a_1792_);
lean_inc(v_a_1791_);
lean_dec(v___x_1790_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1813_;
goto v_resetjp_1793_;
}
v_resetjp_1793_:
{
lean_object* v_quotContext_1796_; lean_object* v_currMacroScope_1797_; lean_object* v_ref_1798_; uint8_t v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1811_; 
v_quotContext_1796_ = lean_ctor_get(v_a_1429_, 1);
lean_inc(v_quotContext_1796_);
v_currMacroScope_1797_ = lean_ctor_get(v_a_1429_, 2);
lean_inc(v_currMacroScope_1797_);
v_ref_1798_ = lean_ctor_get(v_a_1429_, 5);
lean_inc(v_ref_1798_);
lean_dec_ref(v_a_1429_);
v___x_1799_ = 0;
v___x_1800_ = l_Lean_SourceInfo_fromRef(v_ref_1798_, v___x_1799_);
lean_dec(v_ref_1798_);
v___x_1801_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_1802_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__101, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__101_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__101);
v___x_1803_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__103));
v___x_1804_ = l_Lean_addMacroScope(v_quotContext_1796_, v___x_1803_, v_currMacroScope_1797_);
v___x_1805_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__107));
lean_inc(v___x_1800_);
v___x_1806_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1806_, 0, v___x_1800_);
lean_ctor_set(v___x_1806_, 1, v___x_1802_);
lean_ctor_set(v___x_1806_, 2, v___x_1804_);
lean_ctor_set(v___x_1806_, 3, v___x_1805_);
v___x_1807_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
lean_inc(v___x_1800_);
v___x_1808_ = l_Lean_Syntax_node1(v___x_1800_, v___x_1807_, v_a_1791_);
v___x_1809_ = l_Lean_Syntax_node2(v___x_1800_, v___x_1801_, v___x_1806_, v___x_1808_);
if (v_isShared_1795_ == 0)
{
lean_ctor_set(v___x_1794_, 0, v___x_1809_);
v___x_1811_ = v___x_1794_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v___x_1809_);
lean_ctor_set(v_reuseFailAlloc_1812_, 1, v_a_1792_);
v___x_1811_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
return v___x_1811_;
}
}
}
case 9:
{
uint8_t v_presentation_1814_; lean_object* v___x_1815_; lean_object* v_a_1816_; lean_object* v_a_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1838_; 
v_presentation_1814_ = lean_ctor_get_uint8(v_x_1428_, 0);
lean_dec_ref(v_x_1428_);
lean_inc_ref(v_a_1429_);
v___x_1815_ = l___private_Std_Time_Notation_0__Std_Time_convertText(v_presentation_1814_, v_a_1429_, v_a_1430_);
v_a_1816_ = lean_ctor_get(v___x_1815_, 0);
v_a_1817_ = lean_ctor_get(v___x_1815_, 1);
v_isSharedCheck_1838_ = !lean_is_exclusive(v___x_1815_);
if (v_isSharedCheck_1838_ == 0)
{
v___x_1819_ = v___x_1815_;
v_isShared_1820_ = v_isSharedCheck_1838_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_a_1817_);
lean_inc(v_a_1816_);
lean_dec(v___x_1815_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1838_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v_quotContext_1821_; lean_object* v_currMacroScope_1822_; lean_object* v_ref_1823_; uint8_t v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1836_; 
v_quotContext_1821_ = lean_ctor_get(v_a_1429_, 1);
lean_inc(v_quotContext_1821_);
v_currMacroScope_1822_ = lean_ctor_get(v_a_1429_, 2);
lean_inc(v_currMacroScope_1822_);
v_ref_1823_ = lean_ctor_get(v_a_1429_, 5);
lean_inc(v_ref_1823_);
lean_dec_ref(v_a_1429_);
v___x_1824_ = 0;
v___x_1825_ = l_Lean_SourceInfo_fromRef(v_ref_1823_, v___x_1824_);
lean_dec(v_ref_1823_);
v___x_1826_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_1827_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__109, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__109_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__109);
v___x_1828_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__111));
v___x_1829_ = l_Lean_addMacroScope(v_quotContext_1821_, v___x_1828_, v_currMacroScope_1822_);
v___x_1830_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__115));
lean_inc(v___x_1825_);
v___x_1831_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1831_, 0, v___x_1825_);
lean_ctor_set(v___x_1831_, 1, v___x_1827_);
lean_ctor_set(v___x_1831_, 2, v___x_1829_);
lean_ctor_set(v___x_1831_, 3, v___x_1830_);
v___x_1832_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
lean_inc(v___x_1825_);
v___x_1833_ = l_Lean_Syntax_node1(v___x_1825_, v___x_1832_, v_a_1816_);
v___x_1834_ = l_Lean_Syntax_node2(v___x_1825_, v___x_1826_, v___x_1831_, v___x_1833_);
if (v_isShared_1820_ == 0)
{
lean_ctor_set(v___x_1819_, 0, v___x_1834_);
v___x_1836_ = v___x_1819_;
goto v_reusejp_1835_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1837_, 0, v___x_1834_);
lean_ctor_set(v_reuseFailAlloc_1837_, 1, v_a_1817_);
v___x_1836_ = v_reuseFailAlloc_1837_;
goto v_reusejp_1835_;
}
v_reusejp_1835_:
{
return v___x_1836_;
}
}
}
case 10:
{
lean_object* v_presentation_1839_; 
v_presentation_1839_ = lean_ctor_get(v_x_1428_, 0);
lean_inc_ref(v_presentation_1839_);
lean_dec_ref(v_x_1428_);
if (lean_obj_tag(v_presentation_1839_) == 0)
{
lean_object* v_val_1840_; lean_object* v___x_1841_; lean_object* v_a_1842_; lean_object* v_a_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1890_; 
v_val_1840_ = lean_ctor_get(v_presentation_1839_, 0);
lean_inc(v_val_1840_);
lean_dec_ref(v_presentation_1839_);
lean_inc_ref(v_a_1429_);
v___x_1841_ = l___private_Std_Time_Notation_0__Std_Time_convertNumber(v_val_1840_, v_a_1429_, v_a_1430_);
v_a_1842_ = lean_ctor_get(v___x_1841_, 0);
v_a_1843_ = lean_ctor_get(v___x_1841_, 1);
v_isSharedCheck_1890_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_1890_ == 0)
{
v___x_1845_ = v___x_1841_;
v_isShared_1846_ = v_isSharedCheck_1890_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_a_1843_);
lean_inc(v_a_1842_);
lean_dec(v___x_1841_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1890_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
lean_object* v_quotContext_1847_; lean_object* v_currMacroScope_1848_; lean_object* v_ref_1849_; uint8_t v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1888_; 
v_quotContext_1847_ = lean_ctor_get(v_a_1429_, 1);
lean_inc(v_quotContext_1847_);
v_currMacroScope_1848_ = lean_ctor_get(v_a_1429_, 2);
lean_inc(v_currMacroScope_1848_);
v_ref_1849_ = lean_ctor_get(v_a_1429_, 5);
lean_inc(v_ref_1849_);
lean_dec_ref(v_a_1429_);
v___x_1850_ = 0;
v___x_1851_ = l_Lean_SourceInfo_fromRef(v_ref_1849_, v___x_1850_);
lean_dec(v_ref_1849_);
v___x_1852_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_1853_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__117, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__117_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__117);
v___x_1854_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__119));
lean_inc(v_currMacroScope_1848_);
lean_inc(v_quotContext_1847_);
v___x_1855_ = l_Lean_addMacroScope(v_quotContext_1847_, v___x_1854_, v_currMacroScope_1848_);
v___x_1856_ = lean_box(0);
v___x_1857_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__123));
lean_inc(v___x_1851_);
v___x_1858_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1858_, 0, v___x_1851_);
lean_ctor_set(v___x_1858_, 1, v___x_1853_);
lean_ctor_set(v___x_1858_, 2, v___x_1855_);
lean_ctor_set(v___x_1858_, 3, v___x_1857_);
v___x_1859_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_1860_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__42));
v___x_1861_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__44));
v___x_1862_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__45));
lean_inc(v___x_1851_);
v___x_1863_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1863_, 0, v___x_1851_);
lean_ctor_set(v___x_1863_, 1, v___x_1862_);
v___x_1864_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__47));
v___x_1865_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49);
v___x_1866_ = lean_box(0);
lean_inc(v_currMacroScope_1848_);
lean_inc(v_quotContext_1847_);
v___x_1867_ = l_Lean_addMacroScope(v_quotContext_1847_, v___x_1866_, v_currMacroScope_1848_);
v___x_1868_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__65));
lean_inc(v___x_1851_);
v___x_1869_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1869_, 0, v___x_1851_);
lean_ctor_set(v___x_1869_, 1, v___x_1865_);
lean_ctor_set(v___x_1869_, 2, v___x_1867_);
lean_ctor_set(v___x_1869_, 3, v___x_1868_);
lean_inc(v___x_1851_);
v___x_1870_ = l_Lean_Syntax_node1(v___x_1851_, v___x_1864_, v___x_1869_);
lean_inc(v___x_1851_);
v___x_1871_ = l_Lean_Syntax_node2(v___x_1851_, v___x_1861_, v___x_1863_, v___x_1870_);
v___x_1872_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__67));
v___x_1873_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__68));
lean_inc(v___x_1851_);
v___x_1874_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1874_, 0, v___x_1851_);
lean_ctor_set(v___x_1874_, 1, v___x_1873_);
v___x_1875_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__70, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__70_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__70);
v___x_1876_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__71));
v___x_1877_ = l_Lean_addMacroScope(v_quotContext_1847_, v___x_1876_, v_currMacroScope_1848_);
lean_inc(v___x_1851_);
v___x_1878_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1878_, 0, v___x_1851_);
lean_ctor_set(v___x_1878_, 1, v___x_1875_);
lean_ctor_set(v___x_1878_, 2, v___x_1877_);
lean_ctor_set(v___x_1878_, 3, v___x_1856_);
lean_inc(v___x_1851_);
v___x_1879_ = l_Lean_Syntax_node2(v___x_1851_, v___x_1872_, v___x_1874_, v___x_1878_);
lean_inc(v___x_1851_);
v___x_1880_ = l_Lean_Syntax_node1(v___x_1851_, v___x_1859_, v_a_1842_);
lean_inc(v___x_1851_);
v___x_1881_ = l_Lean_Syntax_node2(v___x_1851_, v___x_1852_, v___x_1879_, v___x_1880_);
v___x_1882_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__72));
lean_inc(v___x_1851_);
v___x_1883_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1883_, 0, v___x_1851_);
lean_ctor_set(v___x_1883_, 1, v___x_1882_);
lean_inc(v___x_1851_);
v___x_1884_ = l_Lean_Syntax_node3(v___x_1851_, v___x_1860_, v___x_1871_, v___x_1881_, v___x_1883_);
lean_inc(v___x_1851_);
v___x_1885_ = l_Lean_Syntax_node1(v___x_1851_, v___x_1859_, v___x_1884_);
v___x_1886_ = l_Lean_Syntax_node2(v___x_1851_, v___x_1852_, v___x_1858_, v___x_1885_);
if (v_isShared_1846_ == 0)
{
lean_ctor_set(v___x_1845_, 0, v___x_1886_);
v___x_1888_ = v___x_1845_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v___x_1886_);
lean_ctor_set(v_reuseFailAlloc_1889_, 1, v_a_1843_);
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
lean_object* v_val_1891_; uint8_t v___x_1892_; lean_object* v___x_1893_; lean_object* v_a_1894_; lean_object* v_a_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1942_; 
v_val_1891_ = lean_ctor_get(v_presentation_1839_, 0);
lean_inc(v_val_1891_);
lean_dec_ref(v_presentation_1839_);
v___x_1892_ = lean_unbox(v_val_1891_);
lean_dec(v_val_1891_);
lean_inc_ref(v_a_1429_);
v___x_1893_ = l___private_Std_Time_Notation_0__Std_Time_convertText(v___x_1892_, v_a_1429_, v_a_1430_);
v_a_1894_ = lean_ctor_get(v___x_1893_, 0);
v_a_1895_ = lean_ctor_get(v___x_1893_, 1);
v_isSharedCheck_1942_ = !lean_is_exclusive(v___x_1893_);
if (v_isSharedCheck_1942_ == 0)
{
v___x_1897_ = v___x_1893_;
v_isShared_1898_ = v_isSharedCheck_1942_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_a_1895_);
lean_inc(v_a_1894_);
lean_dec(v___x_1893_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1942_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
lean_object* v_quotContext_1899_; lean_object* v_currMacroScope_1900_; lean_object* v_ref_1901_; uint8_t v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1940_; 
v_quotContext_1899_ = lean_ctor_get(v_a_1429_, 1);
lean_inc(v_quotContext_1899_);
v_currMacroScope_1900_ = lean_ctor_get(v_a_1429_, 2);
lean_inc(v_currMacroScope_1900_);
v_ref_1901_ = lean_ctor_get(v_a_1429_, 5);
lean_inc(v_ref_1901_);
lean_dec_ref(v_a_1429_);
v___x_1902_ = 0;
v___x_1903_ = l_Lean_SourceInfo_fromRef(v_ref_1901_, v___x_1902_);
lean_dec(v_ref_1901_);
v___x_1904_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_1905_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__117, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__117_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__117);
v___x_1906_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__119));
lean_inc(v_currMacroScope_1900_);
lean_inc(v_quotContext_1899_);
v___x_1907_ = l_Lean_addMacroScope(v_quotContext_1899_, v___x_1906_, v_currMacroScope_1900_);
v___x_1908_ = lean_box(0);
v___x_1909_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__123));
lean_inc(v___x_1903_);
v___x_1910_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1910_, 0, v___x_1903_);
lean_ctor_set(v___x_1910_, 1, v___x_1905_);
lean_ctor_set(v___x_1910_, 2, v___x_1907_);
lean_ctor_set(v___x_1910_, 3, v___x_1909_);
v___x_1911_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_1912_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__42));
v___x_1913_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__44));
v___x_1914_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__45));
lean_inc(v___x_1903_);
v___x_1915_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1915_, 0, v___x_1903_);
lean_ctor_set(v___x_1915_, 1, v___x_1914_);
v___x_1916_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__47));
v___x_1917_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49);
v___x_1918_ = lean_box(0);
lean_inc(v_currMacroScope_1900_);
lean_inc(v_quotContext_1899_);
v___x_1919_ = l_Lean_addMacroScope(v_quotContext_1899_, v___x_1918_, v_currMacroScope_1900_);
v___x_1920_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__65));
lean_inc(v___x_1903_);
v___x_1921_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1921_, 0, v___x_1903_);
lean_ctor_set(v___x_1921_, 1, v___x_1917_);
lean_ctor_set(v___x_1921_, 2, v___x_1919_);
lean_ctor_set(v___x_1921_, 3, v___x_1920_);
lean_inc(v___x_1903_);
v___x_1922_ = l_Lean_Syntax_node1(v___x_1903_, v___x_1916_, v___x_1921_);
lean_inc(v___x_1903_);
v___x_1923_ = l_Lean_Syntax_node2(v___x_1903_, v___x_1913_, v___x_1915_, v___x_1922_);
v___x_1924_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__67));
v___x_1925_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__68));
lean_inc(v___x_1903_);
v___x_1926_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1926_, 0, v___x_1903_);
lean_ctor_set(v___x_1926_, 1, v___x_1925_);
v___x_1927_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__74, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__74_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__74);
v___x_1928_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__75));
v___x_1929_ = l_Lean_addMacroScope(v_quotContext_1899_, v___x_1928_, v_currMacroScope_1900_);
lean_inc(v___x_1903_);
v___x_1930_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1930_, 0, v___x_1903_);
lean_ctor_set(v___x_1930_, 1, v___x_1927_);
lean_ctor_set(v___x_1930_, 2, v___x_1929_);
lean_ctor_set(v___x_1930_, 3, v___x_1908_);
lean_inc(v___x_1903_);
v___x_1931_ = l_Lean_Syntax_node2(v___x_1903_, v___x_1924_, v___x_1926_, v___x_1930_);
lean_inc(v___x_1903_);
v___x_1932_ = l_Lean_Syntax_node1(v___x_1903_, v___x_1911_, v_a_1894_);
lean_inc(v___x_1903_);
v___x_1933_ = l_Lean_Syntax_node2(v___x_1903_, v___x_1904_, v___x_1931_, v___x_1932_);
v___x_1934_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__72));
lean_inc(v___x_1903_);
v___x_1935_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1935_, 0, v___x_1903_);
lean_ctor_set(v___x_1935_, 1, v___x_1934_);
lean_inc(v___x_1903_);
v___x_1936_ = l_Lean_Syntax_node3(v___x_1903_, v___x_1912_, v___x_1923_, v___x_1933_, v___x_1935_);
lean_inc(v___x_1903_);
v___x_1937_ = l_Lean_Syntax_node1(v___x_1903_, v___x_1911_, v___x_1936_);
v___x_1938_ = l_Lean_Syntax_node2(v___x_1903_, v___x_1904_, v___x_1910_, v___x_1937_);
if (v_isShared_1898_ == 0)
{
lean_ctor_set(v___x_1897_, 0, v___x_1938_);
v___x_1940_ = v___x_1897_;
goto v_reusejp_1939_;
}
else
{
lean_object* v_reuseFailAlloc_1941_; 
v_reuseFailAlloc_1941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1941_, 0, v___x_1938_);
lean_ctor_set(v_reuseFailAlloc_1941_, 1, v_a_1895_);
v___x_1940_ = v_reuseFailAlloc_1941_;
goto v_reusejp_1939_;
}
v_reusejp_1939_:
{
return v___x_1940_;
}
}
}
}
case 11:
{
lean_object* v_presentation_1943_; lean_object* v___x_1944_; lean_object* v_a_1945_; lean_object* v_a_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1967_; 
v_presentation_1943_ = lean_ctor_get(v_x_1428_, 0);
lean_inc(v_presentation_1943_);
lean_dec_ref(v_x_1428_);
lean_inc_ref(v_a_1429_);
v___x_1944_ = l___private_Std_Time_Notation_0__Std_Time_convertNumber(v_presentation_1943_, v_a_1429_, v_a_1430_);
v_a_1945_ = lean_ctor_get(v___x_1944_, 0);
v_a_1946_ = lean_ctor_get(v___x_1944_, 1);
v_isSharedCheck_1967_ = !lean_is_exclusive(v___x_1944_);
if (v_isSharedCheck_1967_ == 0)
{
v___x_1948_ = v___x_1944_;
v_isShared_1949_ = v_isSharedCheck_1967_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_a_1946_);
lean_inc(v_a_1945_);
lean_dec(v___x_1944_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1967_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
lean_object* v_quotContext_1950_; lean_object* v_currMacroScope_1951_; lean_object* v_ref_1952_; uint8_t v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1965_; 
v_quotContext_1950_ = lean_ctor_get(v_a_1429_, 1);
lean_inc(v_quotContext_1950_);
v_currMacroScope_1951_ = lean_ctor_get(v_a_1429_, 2);
lean_inc(v_currMacroScope_1951_);
v_ref_1952_ = lean_ctor_get(v_a_1429_, 5);
lean_inc(v_ref_1952_);
lean_dec_ref(v_a_1429_);
v___x_1953_ = 0;
v___x_1954_ = l_Lean_SourceInfo_fromRef(v_ref_1952_, v___x_1953_);
lean_dec(v_ref_1952_);
v___x_1955_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_1956_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__125, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__125_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__125);
v___x_1957_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__127));
v___x_1958_ = l_Lean_addMacroScope(v_quotContext_1950_, v___x_1957_, v_currMacroScope_1951_);
v___x_1959_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__131));
lean_inc(v___x_1954_);
v___x_1960_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1960_, 0, v___x_1954_);
lean_ctor_set(v___x_1960_, 1, v___x_1956_);
lean_ctor_set(v___x_1960_, 2, v___x_1958_);
lean_ctor_set(v___x_1960_, 3, v___x_1959_);
v___x_1961_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
lean_inc(v___x_1954_);
v___x_1962_ = l_Lean_Syntax_node1(v___x_1954_, v___x_1961_, v_a_1945_);
v___x_1963_ = l_Lean_Syntax_node2(v___x_1954_, v___x_1955_, v___x_1960_, v___x_1962_);
if (v_isShared_1949_ == 0)
{
lean_ctor_set(v___x_1948_, 0, v___x_1963_);
v___x_1965_ = v___x_1948_;
goto v_reusejp_1964_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v___x_1963_);
lean_ctor_set(v_reuseFailAlloc_1966_, 1, v_a_1946_);
v___x_1965_ = v_reuseFailAlloc_1966_;
goto v_reusejp_1964_;
}
v_reusejp_1964_:
{
return v___x_1965_;
}
}
}
case 12:
{
uint8_t v_presentation_1968_; lean_object* v___x_1969_; lean_object* v_a_1970_; lean_object* v_a_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_1992_; 
v_presentation_1968_ = lean_ctor_get_uint8(v_x_1428_, 0);
lean_dec_ref(v_x_1428_);
lean_inc_ref(v_a_1429_);
v___x_1969_ = l___private_Std_Time_Notation_0__Std_Time_convertText(v_presentation_1968_, v_a_1429_, v_a_1430_);
v_a_1970_ = lean_ctor_get(v___x_1969_, 0);
v_a_1971_ = lean_ctor_get(v___x_1969_, 1);
v_isSharedCheck_1992_ = !lean_is_exclusive(v___x_1969_);
if (v_isSharedCheck_1992_ == 0)
{
v___x_1973_ = v___x_1969_;
v_isShared_1974_ = v_isSharedCheck_1992_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_a_1971_);
lean_inc(v_a_1970_);
lean_dec(v___x_1969_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_1992_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v_quotContext_1975_; lean_object* v_currMacroScope_1976_; lean_object* v_ref_1977_; uint8_t v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1990_; 
v_quotContext_1975_ = lean_ctor_get(v_a_1429_, 1);
lean_inc(v_quotContext_1975_);
v_currMacroScope_1976_ = lean_ctor_get(v_a_1429_, 2);
lean_inc(v_currMacroScope_1976_);
v_ref_1977_ = lean_ctor_get(v_a_1429_, 5);
lean_inc(v_ref_1977_);
lean_dec_ref(v_a_1429_);
v___x_1978_ = 0;
v___x_1979_ = l_Lean_SourceInfo_fromRef(v_ref_1977_, v___x_1978_);
lean_dec(v_ref_1977_);
v___x_1980_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_1981_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__133, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__133_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__133);
v___x_1982_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__135));
v___x_1983_ = l_Lean_addMacroScope(v_quotContext_1975_, v___x_1982_, v_currMacroScope_1976_);
v___x_1984_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__139));
lean_inc(v___x_1979_);
v___x_1985_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1985_, 0, v___x_1979_);
lean_ctor_set(v___x_1985_, 1, v___x_1981_);
lean_ctor_set(v___x_1985_, 2, v___x_1983_);
lean_ctor_set(v___x_1985_, 3, v___x_1984_);
v___x_1986_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
lean_inc(v___x_1979_);
v___x_1987_ = l_Lean_Syntax_node1(v___x_1979_, v___x_1986_, v_a_1970_);
v___x_1988_ = l_Lean_Syntax_node2(v___x_1979_, v___x_1980_, v___x_1985_, v___x_1987_);
if (v_isShared_1974_ == 0)
{
lean_ctor_set(v___x_1973_, 0, v___x_1988_);
v___x_1990_ = v___x_1973_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v___x_1988_);
lean_ctor_set(v_reuseFailAlloc_1991_, 1, v_a_1971_);
v___x_1990_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
return v___x_1990_;
}
}
}
case 13:
{
lean_object* v_presentation_1993_; lean_object* v___x_1994_; lean_object* v_a_1995_; lean_object* v_a_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2017_; 
v_presentation_1993_ = lean_ctor_get(v_x_1428_, 0);
lean_inc(v_presentation_1993_);
lean_dec_ref(v_x_1428_);
lean_inc_ref(v_a_1429_);
v___x_1994_ = l___private_Std_Time_Notation_0__Std_Time_convertNumber(v_presentation_1993_, v_a_1429_, v_a_1430_);
v_a_1995_ = lean_ctor_get(v___x_1994_, 0);
v_a_1996_ = lean_ctor_get(v___x_1994_, 1);
v_isSharedCheck_2017_ = !lean_is_exclusive(v___x_1994_);
if (v_isSharedCheck_2017_ == 0)
{
v___x_1998_ = v___x_1994_;
v_isShared_1999_ = v_isSharedCheck_2017_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_a_1996_);
lean_inc(v_a_1995_);
lean_dec(v___x_1994_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2017_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v_quotContext_2000_; lean_object* v_currMacroScope_2001_; lean_object* v_ref_2002_; uint8_t v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2015_; 
v_quotContext_2000_ = lean_ctor_get(v_a_1429_, 1);
lean_inc(v_quotContext_2000_);
v_currMacroScope_2001_ = lean_ctor_get(v_a_1429_, 2);
lean_inc(v_currMacroScope_2001_);
v_ref_2002_ = lean_ctor_get(v_a_1429_, 5);
lean_inc(v_ref_2002_);
lean_dec_ref(v_a_1429_);
v___x_2003_ = 0;
v___x_2004_ = l_Lean_SourceInfo_fromRef(v_ref_2002_, v___x_2003_);
lean_dec(v_ref_2002_);
v___x_2005_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2006_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__141, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__141_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__141);
v___x_2007_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__143));
v___x_2008_ = l_Lean_addMacroScope(v_quotContext_2000_, v___x_2007_, v_currMacroScope_2001_);
v___x_2009_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__147));
lean_inc(v___x_2004_);
v___x_2010_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2010_, 0, v___x_2004_);
lean_ctor_set(v___x_2010_, 1, v___x_2006_);
lean_ctor_set(v___x_2010_, 2, v___x_2008_);
lean_ctor_set(v___x_2010_, 3, v___x_2009_);
v___x_2011_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
lean_inc(v___x_2004_);
v___x_2012_ = l_Lean_Syntax_node1(v___x_2004_, v___x_2011_, v_a_1995_);
v___x_2013_ = l_Lean_Syntax_node2(v___x_2004_, v___x_2005_, v___x_2010_, v___x_2012_);
if (v_isShared_1999_ == 0)
{
lean_ctor_set(v___x_1998_, 0, v___x_2013_);
v___x_2015_ = v___x_1998_;
goto v_reusejp_2014_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v___x_2013_);
lean_ctor_set(v_reuseFailAlloc_2016_, 1, v_a_1996_);
v___x_2015_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2014_;
}
v_reusejp_2014_:
{
return v___x_2015_;
}
}
}
case 14:
{
lean_object* v_presentation_2018_; lean_object* v___x_2019_; lean_object* v_a_2020_; lean_object* v_a_2021_; lean_object* v___x_2023_; uint8_t v_isShared_2024_; uint8_t v_isSharedCheck_2042_; 
v_presentation_2018_ = lean_ctor_get(v_x_1428_, 0);
lean_inc(v_presentation_2018_);
lean_dec_ref(v_x_1428_);
lean_inc_ref(v_a_1429_);
v___x_2019_ = l___private_Std_Time_Notation_0__Std_Time_convertNumber(v_presentation_2018_, v_a_1429_, v_a_1430_);
v_a_2020_ = lean_ctor_get(v___x_2019_, 0);
v_a_2021_ = lean_ctor_get(v___x_2019_, 1);
v_isSharedCheck_2042_ = !lean_is_exclusive(v___x_2019_);
if (v_isSharedCheck_2042_ == 0)
{
v___x_2023_ = v___x_2019_;
v_isShared_2024_ = v_isSharedCheck_2042_;
goto v_resetjp_2022_;
}
else
{
lean_inc(v_a_2021_);
lean_inc(v_a_2020_);
lean_dec(v___x_2019_);
v___x_2023_ = lean_box(0);
v_isShared_2024_ = v_isSharedCheck_2042_;
goto v_resetjp_2022_;
}
v_resetjp_2022_:
{
lean_object* v_quotContext_2025_; lean_object* v_currMacroScope_2026_; lean_object* v_ref_2027_; uint8_t v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2040_; 
v_quotContext_2025_ = lean_ctor_get(v_a_1429_, 1);
lean_inc(v_quotContext_2025_);
v_currMacroScope_2026_ = lean_ctor_get(v_a_1429_, 2);
lean_inc(v_currMacroScope_2026_);
v_ref_2027_ = lean_ctor_get(v_a_1429_, 5);
lean_inc(v_ref_2027_);
lean_dec_ref(v_a_1429_);
v___x_2028_ = 0;
v___x_2029_ = l_Lean_SourceInfo_fromRef(v_ref_2027_, v___x_2028_);
lean_dec(v_ref_2027_);
v___x_2030_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2031_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__149, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__149_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__149);
v___x_2032_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__151));
v___x_2033_ = l_Lean_addMacroScope(v_quotContext_2025_, v___x_2032_, v_currMacroScope_2026_);
v___x_2034_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__155));
lean_inc(v___x_2029_);
v___x_2035_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2035_, 0, v___x_2029_);
lean_ctor_set(v___x_2035_, 1, v___x_2031_);
lean_ctor_set(v___x_2035_, 2, v___x_2033_);
lean_ctor_set(v___x_2035_, 3, v___x_2034_);
v___x_2036_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
lean_inc(v___x_2029_);
v___x_2037_ = l_Lean_Syntax_node1(v___x_2029_, v___x_2036_, v_a_2020_);
v___x_2038_ = l_Lean_Syntax_node2(v___x_2029_, v___x_2030_, v___x_2035_, v___x_2037_);
if (v_isShared_2024_ == 0)
{
lean_ctor_set(v___x_2023_, 0, v___x_2038_);
v___x_2040_ = v___x_2023_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v___x_2038_);
lean_ctor_set(v_reuseFailAlloc_2041_, 1, v_a_2021_);
v___x_2040_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
return v___x_2040_;
}
}
}
case 15:
{
lean_object* v_presentation_2043_; lean_object* v___x_2044_; lean_object* v_a_2045_; lean_object* v_a_2046_; lean_object* v___x_2048_; uint8_t v_isShared_2049_; uint8_t v_isSharedCheck_2067_; 
v_presentation_2043_ = lean_ctor_get(v_x_1428_, 0);
lean_inc(v_presentation_2043_);
lean_dec_ref(v_x_1428_);
lean_inc_ref(v_a_1429_);
v___x_2044_ = l___private_Std_Time_Notation_0__Std_Time_convertNumber(v_presentation_2043_, v_a_1429_, v_a_1430_);
v_a_2045_ = lean_ctor_get(v___x_2044_, 0);
v_a_2046_ = lean_ctor_get(v___x_2044_, 1);
v_isSharedCheck_2067_ = !lean_is_exclusive(v___x_2044_);
if (v_isSharedCheck_2067_ == 0)
{
v___x_2048_ = v___x_2044_;
v_isShared_2049_ = v_isSharedCheck_2067_;
goto v_resetjp_2047_;
}
else
{
lean_inc(v_a_2046_);
lean_inc(v_a_2045_);
lean_dec(v___x_2044_);
v___x_2048_ = lean_box(0);
v_isShared_2049_ = v_isSharedCheck_2067_;
goto v_resetjp_2047_;
}
v_resetjp_2047_:
{
lean_object* v_quotContext_2050_; lean_object* v_currMacroScope_2051_; lean_object* v_ref_2052_; uint8_t v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2065_; 
v_quotContext_2050_ = lean_ctor_get(v_a_1429_, 1);
lean_inc(v_quotContext_2050_);
v_currMacroScope_2051_ = lean_ctor_get(v_a_1429_, 2);
lean_inc(v_currMacroScope_2051_);
v_ref_2052_ = lean_ctor_get(v_a_1429_, 5);
lean_inc(v_ref_2052_);
lean_dec_ref(v_a_1429_);
v___x_2053_ = 0;
v___x_2054_ = l_Lean_SourceInfo_fromRef(v_ref_2052_, v___x_2053_);
lean_dec(v_ref_2052_);
v___x_2055_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2056_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__157, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__157_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__157);
v___x_2057_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__159));
v___x_2058_ = l_Lean_addMacroScope(v_quotContext_2050_, v___x_2057_, v_currMacroScope_2051_);
v___x_2059_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__163));
lean_inc(v___x_2054_);
v___x_2060_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2060_, 0, v___x_2054_);
lean_ctor_set(v___x_2060_, 1, v___x_2056_);
lean_ctor_set(v___x_2060_, 2, v___x_2058_);
lean_ctor_set(v___x_2060_, 3, v___x_2059_);
v___x_2061_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
lean_inc(v___x_2054_);
v___x_2062_ = l_Lean_Syntax_node1(v___x_2054_, v___x_2061_, v_a_2045_);
v___x_2063_ = l_Lean_Syntax_node2(v___x_2054_, v___x_2055_, v___x_2060_, v___x_2062_);
if (v_isShared_2049_ == 0)
{
lean_ctor_set(v___x_2048_, 0, v___x_2063_);
v___x_2065_ = v___x_2048_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2066_; 
v_reuseFailAlloc_2066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2066_, 0, v___x_2063_);
lean_ctor_set(v_reuseFailAlloc_2066_, 1, v_a_2046_);
v___x_2065_ = v_reuseFailAlloc_2066_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
return v___x_2065_;
}
}
}
case 16:
{
lean_object* v_presentation_2068_; lean_object* v___x_2069_; lean_object* v_a_2070_; lean_object* v_a_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2092_; 
v_presentation_2068_ = lean_ctor_get(v_x_1428_, 0);
lean_inc(v_presentation_2068_);
lean_dec_ref(v_x_1428_);
lean_inc_ref(v_a_1429_);
v___x_2069_ = l___private_Std_Time_Notation_0__Std_Time_convertNumber(v_presentation_2068_, v_a_1429_, v_a_1430_);
v_a_2070_ = lean_ctor_get(v___x_2069_, 0);
v_a_2071_ = lean_ctor_get(v___x_2069_, 1);
v_isSharedCheck_2092_ = !lean_is_exclusive(v___x_2069_);
if (v_isSharedCheck_2092_ == 0)
{
v___x_2073_ = v___x_2069_;
v_isShared_2074_ = v_isSharedCheck_2092_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_a_2071_);
lean_inc(v_a_2070_);
lean_dec(v___x_2069_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2092_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v_quotContext_2075_; lean_object* v_currMacroScope_2076_; lean_object* v_ref_2077_; uint8_t v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2090_; 
v_quotContext_2075_ = lean_ctor_get(v_a_1429_, 1);
lean_inc(v_quotContext_2075_);
v_currMacroScope_2076_ = lean_ctor_get(v_a_1429_, 2);
lean_inc(v_currMacroScope_2076_);
v_ref_2077_ = lean_ctor_get(v_a_1429_, 5);
lean_inc(v_ref_2077_);
lean_dec_ref(v_a_1429_);
v___x_2078_ = 0;
v___x_2079_ = l_Lean_SourceInfo_fromRef(v_ref_2077_, v___x_2078_);
lean_dec(v_ref_2077_);
v___x_2080_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2081_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__165, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__165_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__165);
v___x_2082_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__167));
v___x_2083_ = l_Lean_addMacroScope(v_quotContext_2075_, v___x_2082_, v_currMacroScope_2076_);
v___x_2084_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__171));
lean_inc(v___x_2079_);
v___x_2085_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2085_, 0, v___x_2079_);
lean_ctor_set(v___x_2085_, 1, v___x_2081_);
lean_ctor_set(v___x_2085_, 2, v___x_2083_);
lean_ctor_set(v___x_2085_, 3, v___x_2084_);
v___x_2086_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
lean_inc(v___x_2079_);
v___x_2087_ = l_Lean_Syntax_node1(v___x_2079_, v___x_2086_, v_a_2070_);
v___x_2088_ = l_Lean_Syntax_node2(v___x_2079_, v___x_2080_, v___x_2085_, v___x_2087_);
if (v_isShared_2074_ == 0)
{
lean_ctor_set(v___x_2073_, 0, v___x_2088_);
v___x_2090_ = v___x_2073_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v___x_2088_);
lean_ctor_set(v_reuseFailAlloc_2091_, 1, v_a_2071_);
v___x_2090_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
return v___x_2090_;
}
}
}
case 17:
{
lean_object* v_presentation_2093_; lean_object* v___x_2094_; lean_object* v_a_2095_; lean_object* v_a_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2117_; 
v_presentation_2093_ = lean_ctor_get(v_x_1428_, 0);
lean_inc(v_presentation_2093_);
lean_dec_ref(v_x_1428_);
lean_inc_ref(v_a_1429_);
v___x_2094_ = l___private_Std_Time_Notation_0__Std_Time_convertNumber(v_presentation_2093_, v_a_1429_, v_a_1430_);
v_a_2095_ = lean_ctor_get(v___x_2094_, 0);
v_a_2096_ = lean_ctor_get(v___x_2094_, 1);
v_isSharedCheck_2117_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2117_ == 0)
{
v___x_2098_ = v___x_2094_;
v_isShared_2099_ = v_isSharedCheck_2117_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_a_2096_);
lean_inc(v_a_2095_);
lean_dec(v___x_2094_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2117_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
lean_object* v_quotContext_2100_; lean_object* v_currMacroScope_2101_; lean_object* v_ref_2102_; uint8_t v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2115_; 
v_quotContext_2100_ = lean_ctor_get(v_a_1429_, 1);
lean_inc(v_quotContext_2100_);
v_currMacroScope_2101_ = lean_ctor_get(v_a_1429_, 2);
lean_inc(v_currMacroScope_2101_);
v_ref_2102_ = lean_ctor_get(v_a_1429_, 5);
lean_inc(v_ref_2102_);
lean_dec_ref(v_a_1429_);
v___x_2103_ = 0;
v___x_2104_ = l_Lean_SourceInfo_fromRef(v_ref_2102_, v___x_2103_);
lean_dec(v_ref_2102_);
v___x_2105_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2106_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__173, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__173_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__173);
v___x_2107_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__175));
v___x_2108_ = l_Lean_addMacroScope(v_quotContext_2100_, v___x_2107_, v_currMacroScope_2101_);
v___x_2109_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__179));
lean_inc(v___x_2104_);
v___x_2110_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2110_, 0, v___x_2104_);
lean_ctor_set(v___x_2110_, 1, v___x_2106_);
lean_ctor_set(v___x_2110_, 2, v___x_2108_);
lean_ctor_set(v___x_2110_, 3, v___x_2109_);
v___x_2111_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
lean_inc(v___x_2104_);
v___x_2112_ = l_Lean_Syntax_node1(v___x_2104_, v___x_2111_, v_a_2095_);
v___x_2113_ = l_Lean_Syntax_node2(v___x_2104_, v___x_2105_, v___x_2110_, v___x_2112_);
if (v_isShared_2099_ == 0)
{
lean_ctor_set(v___x_2098_, 0, v___x_2113_);
v___x_2115_ = v___x_2098_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v___x_2113_);
lean_ctor_set(v_reuseFailAlloc_2116_, 1, v_a_2096_);
v___x_2115_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
return v___x_2115_;
}
}
}
case 18:
{
lean_object* v_presentation_2118_; lean_object* v___x_2119_; lean_object* v_a_2120_; lean_object* v_a_2121_; lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2142_; 
v_presentation_2118_ = lean_ctor_get(v_x_1428_, 0);
lean_inc(v_presentation_2118_);
lean_dec_ref(v_x_1428_);
lean_inc_ref(v_a_1429_);
v___x_2119_ = l___private_Std_Time_Notation_0__Std_Time_convertNumber(v_presentation_2118_, v_a_1429_, v_a_1430_);
v_a_2120_ = lean_ctor_get(v___x_2119_, 0);
v_a_2121_ = lean_ctor_get(v___x_2119_, 1);
v_isSharedCheck_2142_ = !lean_is_exclusive(v___x_2119_);
if (v_isSharedCheck_2142_ == 0)
{
v___x_2123_ = v___x_2119_;
v_isShared_2124_ = v_isSharedCheck_2142_;
goto v_resetjp_2122_;
}
else
{
lean_inc(v_a_2121_);
lean_inc(v_a_2120_);
lean_dec(v___x_2119_);
v___x_2123_ = lean_box(0);
v_isShared_2124_ = v_isSharedCheck_2142_;
goto v_resetjp_2122_;
}
v_resetjp_2122_:
{
lean_object* v_quotContext_2125_; lean_object* v_currMacroScope_2126_; lean_object* v_ref_2127_; uint8_t v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2140_; 
v_quotContext_2125_ = lean_ctor_get(v_a_1429_, 1);
lean_inc(v_quotContext_2125_);
v_currMacroScope_2126_ = lean_ctor_get(v_a_1429_, 2);
lean_inc(v_currMacroScope_2126_);
v_ref_2127_ = lean_ctor_get(v_a_1429_, 5);
lean_inc(v_ref_2127_);
lean_dec_ref(v_a_1429_);
v___x_2128_ = 0;
v___x_2129_ = l_Lean_SourceInfo_fromRef(v_ref_2127_, v___x_2128_);
lean_dec(v_ref_2127_);
v___x_2130_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2131_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__181, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__181_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__181);
v___x_2132_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__183));
v___x_2133_ = l_Lean_addMacroScope(v_quotContext_2125_, v___x_2132_, v_currMacroScope_2126_);
v___x_2134_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__187));
lean_inc(v___x_2129_);
v___x_2135_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2135_, 0, v___x_2129_);
lean_ctor_set(v___x_2135_, 1, v___x_2131_);
lean_ctor_set(v___x_2135_, 2, v___x_2133_);
lean_ctor_set(v___x_2135_, 3, v___x_2134_);
v___x_2136_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
lean_inc(v___x_2129_);
v___x_2137_ = l_Lean_Syntax_node1(v___x_2129_, v___x_2136_, v_a_2120_);
v___x_2138_ = l_Lean_Syntax_node2(v___x_2129_, v___x_2130_, v___x_2135_, v___x_2137_);
if (v_isShared_2124_ == 0)
{
lean_ctor_set(v___x_2123_, 0, v___x_2138_);
v___x_2140_ = v___x_2123_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v___x_2138_);
lean_ctor_set(v_reuseFailAlloc_2141_, 1, v_a_2121_);
v___x_2140_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
return v___x_2140_;
}
}
}
case 19:
{
lean_object* v_presentation_2143_; lean_object* v___x_2144_; lean_object* v_a_2145_; lean_object* v_a_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2167_; 
v_presentation_2143_ = lean_ctor_get(v_x_1428_, 0);
lean_inc(v_presentation_2143_);
lean_dec_ref(v_x_1428_);
lean_inc_ref(v_a_1429_);
v___x_2144_ = l___private_Std_Time_Notation_0__Std_Time_convertFraction(v_presentation_2143_, v_a_1429_, v_a_1430_);
v_a_2145_ = lean_ctor_get(v___x_2144_, 0);
v_a_2146_ = lean_ctor_get(v___x_2144_, 1);
v_isSharedCheck_2167_ = !lean_is_exclusive(v___x_2144_);
if (v_isSharedCheck_2167_ == 0)
{
v___x_2148_ = v___x_2144_;
v_isShared_2149_ = v_isSharedCheck_2167_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_a_2146_);
lean_inc(v_a_2145_);
lean_dec(v___x_2144_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2167_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
lean_object* v_quotContext_2150_; lean_object* v_currMacroScope_2151_; lean_object* v_ref_2152_; uint8_t v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2165_; 
v_quotContext_2150_ = lean_ctor_get(v_a_1429_, 1);
lean_inc(v_quotContext_2150_);
v_currMacroScope_2151_ = lean_ctor_get(v_a_1429_, 2);
lean_inc(v_currMacroScope_2151_);
v_ref_2152_ = lean_ctor_get(v_a_1429_, 5);
lean_inc(v_ref_2152_);
lean_dec_ref(v_a_1429_);
v___x_2153_ = 0;
v___x_2154_ = l_Lean_SourceInfo_fromRef(v_ref_2152_, v___x_2153_);
lean_dec(v_ref_2152_);
v___x_2155_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2156_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__189, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__189_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__189);
v___x_2157_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__191));
v___x_2158_ = l_Lean_addMacroScope(v_quotContext_2150_, v___x_2157_, v_currMacroScope_2151_);
v___x_2159_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__195));
lean_inc(v___x_2154_);
v___x_2160_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2160_, 0, v___x_2154_);
lean_ctor_set(v___x_2160_, 1, v___x_2156_);
lean_ctor_set(v___x_2160_, 2, v___x_2158_);
lean_ctor_set(v___x_2160_, 3, v___x_2159_);
v___x_2161_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
lean_inc(v___x_2154_);
v___x_2162_ = l_Lean_Syntax_node1(v___x_2154_, v___x_2161_, v_a_2145_);
v___x_2163_ = l_Lean_Syntax_node2(v___x_2154_, v___x_2155_, v___x_2160_, v___x_2162_);
if (v_isShared_2149_ == 0)
{
lean_ctor_set(v___x_2148_, 0, v___x_2163_);
v___x_2165_ = v___x_2148_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v___x_2163_);
lean_ctor_set(v_reuseFailAlloc_2166_, 1, v_a_2146_);
v___x_2165_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
return v___x_2165_;
}
}
}
case 20:
{
lean_object* v_presentation_2168_; lean_object* v___x_2169_; lean_object* v_a_2170_; lean_object* v_a_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2192_; 
v_presentation_2168_ = lean_ctor_get(v_x_1428_, 0);
lean_inc(v_presentation_2168_);
lean_dec_ref(v_x_1428_);
lean_inc_ref(v_a_1429_);
v___x_2169_ = l___private_Std_Time_Notation_0__Std_Time_convertNumber(v_presentation_2168_, v_a_1429_, v_a_1430_);
v_a_2170_ = lean_ctor_get(v___x_2169_, 0);
v_a_2171_ = lean_ctor_get(v___x_2169_, 1);
v_isSharedCheck_2192_ = !lean_is_exclusive(v___x_2169_);
if (v_isSharedCheck_2192_ == 0)
{
v___x_2173_ = v___x_2169_;
v_isShared_2174_ = v_isSharedCheck_2192_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_a_2171_);
lean_inc(v_a_2170_);
lean_dec(v___x_2169_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2192_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
lean_object* v_quotContext_2175_; lean_object* v_currMacroScope_2176_; lean_object* v_ref_2177_; uint8_t v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2190_; 
v_quotContext_2175_ = lean_ctor_get(v_a_1429_, 1);
lean_inc(v_quotContext_2175_);
v_currMacroScope_2176_ = lean_ctor_get(v_a_1429_, 2);
lean_inc(v_currMacroScope_2176_);
v_ref_2177_ = lean_ctor_get(v_a_1429_, 5);
lean_inc(v_ref_2177_);
lean_dec_ref(v_a_1429_);
v___x_2178_ = 0;
v___x_2179_ = l_Lean_SourceInfo_fromRef(v_ref_2177_, v___x_2178_);
lean_dec(v_ref_2177_);
v___x_2180_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2181_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__197, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__197_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__197);
v___x_2182_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__199));
v___x_2183_ = l_Lean_addMacroScope(v_quotContext_2175_, v___x_2182_, v_currMacroScope_2176_);
v___x_2184_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__203));
lean_inc(v___x_2179_);
v___x_2185_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2185_, 0, v___x_2179_);
lean_ctor_set(v___x_2185_, 1, v___x_2181_);
lean_ctor_set(v___x_2185_, 2, v___x_2183_);
lean_ctor_set(v___x_2185_, 3, v___x_2184_);
v___x_2186_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
lean_inc(v___x_2179_);
v___x_2187_ = l_Lean_Syntax_node1(v___x_2179_, v___x_2186_, v_a_2170_);
v___x_2188_ = l_Lean_Syntax_node2(v___x_2179_, v___x_2180_, v___x_2185_, v___x_2187_);
if (v_isShared_2174_ == 0)
{
lean_ctor_set(v___x_2173_, 0, v___x_2188_);
v___x_2190_ = v___x_2173_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v___x_2188_);
lean_ctor_set(v_reuseFailAlloc_2191_, 1, v_a_2171_);
v___x_2190_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2189_;
}
v_reusejp_2189_:
{
return v___x_2190_;
}
}
}
case 21:
{
lean_object* v_presentation_2193_; lean_object* v___x_2194_; lean_object* v_a_2195_; lean_object* v_a_2196_; lean_object* v___x_2198_; uint8_t v_isShared_2199_; uint8_t v_isSharedCheck_2217_; 
v_presentation_2193_ = lean_ctor_get(v_x_1428_, 0);
lean_inc(v_presentation_2193_);
lean_dec_ref(v_x_1428_);
lean_inc_ref(v_a_1429_);
v___x_2194_ = l___private_Std_Time_Notation_0__Std_Time_convertNumber(v_presentation_2193_, v_a_1429_, v_a_1430_);
v_a_2195_ = lean_ctor_get(v___x_2194_, 0);
v_a_2196_ = lean_ctor_get(v___x_2194_, 1);
v_isSharedCheck_2217_ = !lean_is_exclusive(v___x_2194_);
if (v_isSharedCheck_2217_ == 0)
{
v___x_2198_ = v___x_2194_;
v_isShared_2199_ = v_isSharedCheck_2217_;
goto v_resetjp_2197_;
}
else
{
lean_inc(v_a_2196_);
lean_inc(v_a_2195_);
lean_dec(v___x_2194_);
v___x_2198_ = lean_box(0);
v_isShared_2199_ = v_isSharedCheck_2217_;
goto v_resetjp_2197_;
}
v_resetjp_2197_:
{
lean_object* v_quotContext_2200_; lean_object* v_currMacroScope_2201_; lean_object* v_ref_2202_; uint8_t v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2215_; 
v_quotContext_2200_ = lean_ctor_get(v_a_1429_, 1);
lean_inc(v_quotContext_2200_);
v_currMacroScope_2201_ = lean_ctor_get(v_a_1429_, 2);
lean_inc(v_currMacroScope_2201_);
v_ref_2202_ = lean_ctor_get(v_a_1429_, 5);
lean_inc(v_ref_2202_);
lean_dec_ref(v_a_1429_);
v___x_2203_ = 0;
v___x_2204_ = l_Lean_SourceInfo_fromRef(v_ref_2202_, v___x_2203_);
lean_dec(v_ref_2202_);
v___x_2205_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2206_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__205, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__205_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__205);
v___x_2207_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__207));
v___x_2208_ = l_Lean_addMacroScope(v_quotContext_2200_, v___x_2207_, v_currMacroScope_2201_);
v___x_2209_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__211));
lean_inc(v___x_2204_);
v___x_2210_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2210_, 0, v___x_2204_);
lean_ctor_set(v___x_2210_, 1, v___x_2206_);
lean_ctor_set(v___x_2210_, 2, v___x_2208_);
lean_ctor_set(v___x_2210_, 3, v___x_2209_);
v___x_2211_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
lean_inc(v___x_2204_);
v___x_2212_ = l_Lean_Syntax_node1(v___x_2204_, v___x_2211_, v_a_2195_);
v___x_2213_ = l_Lean_Syntax_node2(v___x_2204_, v___x_2205_, v___x_2210_, v___x_2212_);
if (v_isShared_2199_ == 0)
{
lean_ctor_set(v___x_2198_, 0, v___x_2213_);
v___x_2215_ = v___x_2198_;
goto v_reusejp_2214_;
}
else
{
lean_object* v_reuseFailAlloc_2216_; 
v_reuseFailAlloc_2216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2216_, 0, v___x_2213_);
lean_ctor_set(v_reuseFailAlloc_2216_, 1, v_a_2196_);
v___x_2215_ = v_reuseFailAlloc_2216_;
goto v_reusejp_2214_;
}
v_reusejp_2214_:
{
return v___x_2215_;
}
}
}
case 22:
{
lean_object* v_presentation_2218_; lean_object* v___x_2219_; lean_object* v_a_2220_; lean_object* v_a_2221_; lean_object* v___x_2223_; uint8_t v_isShared_2224_; uint8_t v_isSharedCheck_2242_; 
v_presentation_2218_ = lean_ctor_get(v_x_1428_, 0);
lean_inc(v_presentation_2218_);
lean_dec_ref(v_x_1428_);
lean_inc_ref(v_a_1429_);
v___x_2219_ = l___private_Std_Time_Notation_0__Std_Time_convertNumber(v_presentation_2218_, v_a_1429_, v_a_1430_);
v_a_2220_ = lean_ctor_get(v___x_2219_, 0);
v_a_2221_ = lean_ctor_get(v___x_2219_, 1);
v_isSharedCheck_2242_ = !lean_is_exclusive(v___x_2219_);
if (v_isSharedCheck_2242_ == 0)
{
v___x_2223_ = v___x_2219_;
v_isShared_2224_ = v_isSharedCheck_2242_;
goto v_resetjp_2222_;
}
else
{
lean_inc(v_a_2221_);
lean_inc(v_a_2220_);
lean_dec(v___x_2219_);
v___x_2223_ = lean_box(0);
v_isShared_2224_ = v_isSharedCheck_2242_;
goto v_resetjp_2222_;
}
v_resetjp_2222_:
{
lean_object* v_quotContext_2225_; lean_object* v_currMacroScope_2226_; lean_object* v_ref_2227_; uint8_t v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2240_; 
v_quotContext_2225_ = lean_ctor_get(v_a_1429_, 1);
lean_inc(v_quotContext_2225_);
v_currMacroScope_2226_ = lean_ctor_get(v_a_1429_, 2);
lean_inc(v_currMacroScope_2226_);
v_ref_2227_ = lean_ctor_get(v_a_1429_, 5);
lean_inc(v_ref_2227_);
lean_dec_ref(v_a_1429_);
v___x_2228_ = 0;
v___x_2229_ = l_Lean_SourceInfo_fromRef(v_ref_2227_, v___x_2228_);
lean_dec(v_ref_2227_);
v___x_2230_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2231_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__213, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__213_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__213);
v___x_2232_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__215));
v___x_2233_ = l_Lean_addMacroScope(v_quotContext_2225_, v___x_2232_, v_currMacroScope_2226_);
v___x_2234_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__219));
lean_inc(v___x_2229_);
v___x_2235_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2235_, 0, v___x_2229_);
lean_ctor_set(v___x_2235_, 1, v___x_2231_);
lean_ctor_set(v___x_2235_, 2, v___x_2233_);
lean_ctor_set(v___x_2235_, 3, v___x_2234_);
v___x_2236_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
lean_inc(v___x_2229_);
v___x_2237_ = l_Lean_Syntax_node1(v___x_2229_, v___x_2236_, v_a_2220_);
v___x_2238_ = l_Lean_Syntax_node2(v___x_2229_, v___x_2230_, v___x_2235_, v___x_2237_);
if (v_isShared_2224_ == 0)
{
lean_ctor_set(v___x_2223_, 0, v___x_2238_);
v___x_2240_ = v___x_2223_;
goto v_reusejp_2239_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v___x_2238_);
lean_ctor_set(v_reuseFailAlloc_2241_, 1, v_a_2221_);
v___x_2240_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2239_;
}
v_reusejp_2239_:
{
return v___x_2240_;
}
}
}
case 23:
{
lean_object* v_quotContext_2243_; lean_object* v_currMacroScope_2244_; lean_object* v_ref_2245_; uint8_t v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; 
v_quotContext_2243_ = lean_ctor_get(v_a_1429_, 1);
lean_inc(v_quotContext_2243_);
v_currMacroScope_2244_ = lean_ctor_get(v_a_1429_, 2);
lean_inc(v_currMacroScope_2244_);
v_ref_2245_ = lean_ctor_get(v_a_1429_, 5);
lean_inc(v_ref_2245_);
lean_dec_ref(v_a_1429_);
v___x_2246_ = 0;
v___x_2247_ = l_Lean_SourceInfo_fromRef(v_ref_2245_, v___x_2246_);
lean_dec(v_ref_2245_);
v___x_2248_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__221, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__221_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__221);
v___x_2249_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__223));
v___x_2250_ = l_Lean_addMacroScope(v_quotContext_2243_, v___x_2249_, v_currMacroScope_2244_);
v___x_2251_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__227));
v___x_2252_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2252_, 0, v___x_2247_);
lean_ctor_set(v___x_2252_, 1, v___x_2248_);
lean_ctor_set(v___x_2252_, 2, v___x_2250_);
lean_ctor_set(v___x_2252_, 3, v___x_2251_);
v___x_2253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2253_, 0, v___x_2252_);
lean_ctor_set(v___x_2253_, 1, v_a_1430_);
return v___x_2253_;
}
case 24:
{
uint8_t v_presentation_2254_; lean_object* v___x_2255_; lean_object* v_a_2256_; lean_object* v_a_2257_; lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2278_; 
v_presentation_2254_ = lean_ctor_get_uint8(v_x_1428_, 0);
lean_dec_ref(v_x_1428_);
lean_inc_ref(v_a_1429_);
v___x_2255_ = l___private_Std_Time_Notation_0__Std_Time_convertZoneName(v_presentation_2254_, v_a_1429_, v_a_1430_);
v_a_2256_ = lean_ctor_get(v___x_2255_, 0);
v_a_2257_ = lean_ctor_get(v___x_2255_, 1);
v_isSharedCheck_2278_ = !lean_is_exclusive(v___x_2255_);
if (v_isSharedCheck_2278_ == 0)
{
v___x_2259_ = v___x_2255_;
v_isShared_2260_ = v_isSharedCheck_2278_;
goto v_resetjp_2258_;
}
else
{
lean_inc(v_a_2257_);
lean_inc(v_a_2256_);
lean_dec(v___x_2255_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2278_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
lean_object* v_quotContext_2261_; lean_object* v_currMacroScope_2262_; lean_object* v_ref_2263_; uint8_t v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2276_; 
v_quotContext_2261_ = lean_ctor_get(v_a_1429_, 1);
lean_inc(v_quotContext_2261_);
v_currMacroScope_2262_ = lean_ctor_get(v_a_1429_, 2);
lean_inc(v_currMacroScope_2262_);
v_ref_2263_ = lean_ctor_get(v_a_1429_, 5);
lean_inc(v_ref_2263_);
lean_dec_ref(v_a_1429_);
v___x_2264_ = 0;
v___x_2265_ = l_Lean_SourceInfo_fromRef(v_ref_2263_, v___x_2264_);
lean_dec(v_ref_2263_);
v___x_2266_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2267_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__229, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__229_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__229);
v___x_2268_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__231));
v___x_2269_ = l_Lean_addMacroScope(v_quotContext_2261_, v___x_2268_, v_currMacroScope_2262_);
v___x_2270_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__235));
lean_inc(v___x_2265_);
v___x_2271_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2271_, 0, v___x_2265_);
lean_ctor_set(v___x_2271_, 1, v___x_2267_);
lean_ctor_set(v___x_2271_, 2, v___x_2269_);
lean_ctor_set(v___x_2271_, 3, v___x_2270_);
v___x_2272_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
lean_inc(v___x_2265_);
v___x_2273_ = l_Lean_Syntax_node1(v___x_2265_, v___x_2272_, v_a_2256_);
v___x_2274_ = l_Lean_Syntax_node2(v___x_2265_, v___x_2266_, v___x_2271_, v___x_2273_);
if (v_isShared_2260_ == 0)
{
lean_ctor_set(v___x_2259_, 0, v___x_2274_);
v___x_2276_ = v___x_2259_;
goto v_reusejp_2275_;
}
else
{
lean_object* v_reuseFailAlloc_2277_; 
v_reuseFailAlloc_2277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2277_, 0, v___x_2274_);
lean_ctor_set(v_reuseFailAlloc_2277_, 1, v_a_2257_);
v___x_2276_ = v_reuseFailAlloc_2277_;
goto v_reusejp_2275_;
}
v_reusejp_2275_:
{
return v___x_2276_;
}
}
}
case 25:
{
uint8_t v_presentation_2279_; lean_object* v___x_2280_; lean_object* v_a_2281_; lean_object* v_a_2282_; lean_object* v___x_2284_; uint8_t v_isShared_2285_; uint8_t v_isSharedCheck_2303_; 
v_presentation_2279_ = lean_ctor_get_uint8(v_x_1428_, 0);
lean_dec_ref(v_x_1428_);
lean_inc_ref(v_a_1429_);
v___x_2280_ = l___private_Std_Time_Notation_0__Std_Time_convertOffsetO(v_presentation_2279_, v_a_1429_, v_a_1430_);
v_a_2281_ = lean_ctor_get(v___x_2280_, 0);
v_a_2282_ = lean_ctor_get(v___x_2280_, 1);
v_isSharedCheck_2303_ = !lean_is_exclusive(v___x_2280_);
if (v_isSharedCheck_2303_ == 0)
{
v___x_2284_ = v___x_2280_;
v_isShared_2285_ = v_isSharedCheck_2303_;
goto v_resetjp_2283_;
}
else
{
lean_inc(v_a_2282_);
lean_inc(v_a_2281_);
lean_dec(v___x_2280_);
v___x_2284_ = lean_box(0);
v_isShared_2285_ = v_isSharedCheck_2303_;
goto v_resetjp_2283_;
}
v_resetjp_2283_:
{
lean_object* v_quotContext_2286_; lean_object* v_currMacroScope_2287_; lean_object* v_ref_2288_; uint8_t v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2301_; 
v_quotContext_2286_ = lean_ctor_get(v_a_1429_, 1);
lean_inc(v_quotContext_2286_);
v_currMacroScope_2287_ = lean_ctor_get(v_a_1429_, 2);
lean_inc(v_currMacroScope_2287_);
v_ref_2288_ = lean_ctor_get(v_a_1429_, 5);
lean_inc(v_ref_2288_);
lean_dec_ref(v_a_1429_);
v___x_2289_ = 0;
v___x_2290_ = l_Lean_SourceInfo_fromRef(v_ref_2288_, v___x_2289_);
lean_dec(v_ref_2288_);
v___x_2291_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2292_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__237, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__237_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__237);
v___x_2293_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__239));
v___x_2294_ = l_Lean_addMacroScope(v_quotContext_2286_, v___x_2293_, v_currMacroScope_2287_);
v___x_2295_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__243));
lean_inc(v___x_2290_);
v___x_2296_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2296_, 0, v___x_2290_);
lean_ctor_set(v___x_2296_, 1, v___x_2292_);
lean_ctor_set(v___x_2296_, 2, v___x_2294_);
lean_ctor_set(v___x_2296_, 3, v___x_2295_);
v___x_2297_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
lean_inc(v___x_2290_);
v___x_2298_ = l_Lean_Syntax_node1(v___x_2290_, v___x_2297_, v_a_2281_);
v___x_2299_ = l_Lean_Syntax_node2(v___x_2290_, v___x_2291_, v___x_2296_, v___x_2298_);
if (v_isShared_2285_ == 0)
{
lean_ctor_set(v___x_2284_, 0, v___x_2299_);
v___x_2301_ = v___x_2284_;
goto v_reusejp_2300_;
}
else
{
lean_object* v_reuseFailAlloc_2302_; 
v_reuseFailAlloc_2302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2302_, 0, v___x_2299_);
lean_ctor_set(v_reuseFailAlloc_2302_, 1, v_a_2282_);
v___x_2301_ = v_reuseFailAlloc_2302_;
goto v_reusejp_2300_;
}
v_reusejp_2300_:
{
return v___x_2301_;
}
}
}
case 26:
{
uint8_t v_presentation_2304_; lean_object* v___x_2305_; lean_object* v_a_2306_; lean_object* v_a_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2328_; 
v_presentation_2304_ = lean_ctor_get_uint8(v_x_1428_, 0);
lean_dec_ref(v_x_1428_);
lean_inc_ref(v_a_1429_);
v___x_2305_ = l___private_Std_Time_Notation_0__Std_Time_convertOffsetX(v_presentation_2304_, v_a_1429_, v_a_1430_);
v_a_2306_ = lean_ctor_get(v___x_2305_, 0);
v_a_2307_ = lean_ctor_get(v___x_2305_, 1);
v_isSharedCheck_2328_ = !lean_is_exclusive(v___x_2305_);
if (v_isSharedCheck_2328_ == 0)
{
v___x_2309_ = v___x_2305_;
v_isShared_2310_ = v_isSharedCheck_2328_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_a_2307_);
lean_inc(v_a_2306_);
lean_dec(v___x_2305_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2328_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
lean_object* v_quotContext_2311_; lean_object* v_currMacroScope_2312_; lean_object* v_ref_2313_; uint8_t v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2326_; 
v_quotContext_2311_ = lean_ctor_get(v_a_1429_, 1);
lean_inc(v_quotContext_2311_);
v_currMacroScope_2312_ = lean_ctor_get(v_a_1429_, 2);
lean_inc(v_currMacroScope_2312_);
v_ref_2313_ = lean_ctor_get(v_a_1429_, 5);
lean_inc(v_ref_2313_);
lean_dec_ref(v_a_1429_);
v___x_2314_ = 0;
v___x_2315_ = l_Lean_SourceInfo_fromRef(v_ref_2313_, v___x_2314_);
lean_dec(v_ref_2313_);
v___x_2316_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2317_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__245, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__245_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__245);
v___x_2318_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__247));
v___x_2319_ = l_Lean_addMacroScope(v_quotContext_2311_, v___x_2318_, v_currMacroScope_2312_);
v___x_2320_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__251));
lean_inc(v___x_2315_);
v___x_2321_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2321_, 0, v___x_2315_);
lean_ctor_set(v___x_2321_, 1, v___x_2317_);
lean_ctor_set(v___x_2321_, 2, v___x_2319_);
lean_ctor_set(v___x_2321_, 3, v___x_2320_);
v___x_2322_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
lean_inc(v___x_2315_);
v___x_2323_ = l_Lean_Syntax_node1(v___x_2315_, v___x_2322_, v_a_2306_);
v___x_2324_ = l_Lean_Syntax_node2(v___x_2315_, v___x_2316_, v___x_2321_, v___x_2323_);
if (v_isShared_2310_ == 0)
{
lean_ctor_set(v___x_2309_, 0, v___x_2324_);
v___x_2326_ = v___x_2309_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v___x_2324_);
lean_ctor_set(v_reuseFailAlloc_2327_, 1, v_a_2307_);
v___x_2326_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2325_;
}
v_reusejp_2325_:
{
return v___x_2326_;
}
}
}
case 27:
{
uint8_t v_presentation_2329_; lean_object* v___x_2330_; lean_object* v_a_2331_; lean_object* v_a_2332_; lean_object* v___x_2334_; uint8_t v_isShared_2335_; uint8_t v_isSharedCheck_2353_; 
v_presentation_2329_ = lean_ctor_get_uint8(v_x_1428_, 0);
lean_dec_ref(v_x_1428_);
lean_inc_ref(v_a_1429_);
v___x_2330_ = l___private_Std_Time_Notation_0__Std_Time_convertOffsetX(v_presentation_2329_, v_a_1429_, v_a_1430_);
v_a_2331_ = lean_ctor_get(v___x_2330_, 0);
v_a_2332_ = lean_ctor_get(v___x_2330_, 1);
v_isSharedCheck_2353_ = !lean_is_exclusive(v___x_2330_);
if (v_isSharedCheck_2353_ == 0)
{
v___x_2334_ = v___x_2330_;
v_isShared_2335_ = v_isSharedCheck_2353_;
goto v_resetjp_2333_;
}
else
{
lean_inc(v_a_2332_);
lean_inc(v_a_2331_);
lean_dec(v___x_2330_);
v___x_2334_ = lean_box(0);
v_isShared_2335_ = v_isSharedCheck_2353_;
goto v_resetjp_2333_;
}
v_resetjp_2333_:
{
lean_object* v_quotContext_2336_; lean_object* v_currMacroScope_2337_; lean_object* v_ref_2338_; uint8_t v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2351_; 
v_quotContext_2336_ = lean_ctor_get(v_a_1429_, 1);
lean_inc(v_quotContext_2336_);
v_currMacroScope_2337_ = lean_ctor_get(v_a_1429_, 2);
lean_inc(v_currMacroScope_2337_);
v_ref_2338_ = lean_ctor_get(v_a_1429_, 5);
lean_inc(v_ref_2338_);
lean_dec_ref(v_a_1429_);
v___x_2339_ = 0;
v___x_2340_ = l_Lean_SourceInfo_fromRef(v_ref_2338_, v___x_2339_);
lean_dec(v_ref_2338_);
v___x_2341_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2342_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__253, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__253_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__253);
v___x_2343_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__255));
v___x_2344_ = l_Lean_addMacroScope(v_quotContext_2336_, v___x_2343_, v_currMacroScope_2337_);
v___x_2345_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__259));
lean_inc(v___x_2340_);
v___x_2346_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2346_, 0, v___x_2340_);
lean_ctor_set(v___x_2346_, 1, v___x_2342_);
lean_ctor_set(v___x_2346_, 2, v___x_2344_);
lean_ctor_set(v___x_2346_, 3, v___x_2345_);
v___x_2347_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
lean_inc(v___x_2340_);
v___x_2348_ = l_Lean_Syntax_node1(v___x_2340_, v___x_2347_, v_a_2331_);
v___x_2349_ = l_Lean_Syntax_node2(v___x_2340_, v___x_2341_, v___x_2346_, v___x_2348_);
if (v_isShared_2335_ == 0)
{
lean_ctor_set(v___x_2334_, 0, v___x_2349_);
v___x_2351_ = v___x_2334_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v___x_2349_);
lean_ctor_set(v_reuseFailAlloc_2352_, 1, v_a_2332_);
v___x_2351_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
return v___x_2351_;
}
}
}
default: 
{
uint8_t v_presentation_2354_; lean_object* v___x_2355_; lean_object* v_a_2356_; lean_object* v_a_2357_; lean_object* v___x_2359_; uint8_t v_isShared_2360_; uint8_t v_isSharedCheck_2378_; 
v_presentation_2354_ = lean_ctor_get_uint8(v_x_1428_, 0);
lean_dec_ref(v_x_1428_);
lean_inc_ref(v_a_1429_);
v___x_2355_ = l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ(v_presentation_2354_, v_a_1429_, v_a_1430_);
v_a_2356_ = lean_ctor_get(v___x_2355_, 0);
v_a_2357_ = lean_ctor_get(v___x_2355_, 1);
v_isSharedCheck_2378_ = !lean_is_exclusive(v___x_2355_);
if (v_isSharedCheck_2378_ == 0)
{
v___x_2359_ = v___x_2355_;
v_isShared_2360_ = v_isSharedCheck_2378_;
goto v_resetjp_2358_;
}
else
{
lean_inc(v_a_2357_);
lean_inc(v_a_2356_);
lean_dec(v___x_2355_);
v___x_2359_ = lean_box(0);
v_isShared_2360_ = v_isSharedCheck_2378_;
goto v_resetjp_2358_;
}
v_resetjp_2358_:
{
lean_object* v_quotContext_2361_; lean_object* v_currMacroScope_2362_; lean_object* v_ref_2363_; uint8_t v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2376_; 
v_quotContext_2361_ = lean_ctor_get(v_a_1429_, 1);
lean_inc(v_quotContext_2361_);
v_currMacroScope_2362_ = lean_ctor_get(v_a_1429_, 2);
lean_inc(v_currMacroScope_2362_);
v_ref_2363_ = lean_ctor_get(v_a_1429_, 5);
lean_inc(v_ref_2363_);
lean_dec_ref(v_a_1429_);
v___x_2364_ = 0;
v___x_2365_ = l_Lean_SourceInfo_fromRef(v_ref_2363_, v___x_2364_);
lean_dec(v_ref_2363_);
v___x_2366_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2367_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__261, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__261_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__261);
v___x_2368_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__263));
v___x_2369_ = l_Lean_addMacroScope(v_quotContext_2361_, v___x_2368_, v_currMacroScope_2362_);
v___x_2370_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__267));
lean_inc(v___x_2365_);
v___x_2371_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2371_, 0, v___x_2365_);
lean_ctor_set(v___x_2371_, 1, v___x_2367_);
lean_ctor_set(v___x_2371_, 2, v___x_2369_);
lean_ctor_set(v___x_2371_, 3, v___x_2370_);
v___x_2372_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
lean_inc(v___x_2365_);
v___x_2373_ = l_Lean_Syntax_node1(v___x_2365_, v___x_2372_, v_a_2356_);
v___x_2374_ = l_Lean_Syntax_node2(v___x_2365_, v___x_2366_, v___x_2371_, v___x_2373_);
if (v_isShared_2360_ == 0)
{
lean_ctor_set(v___x_2359_, 0, v___x_2374_);
v___x_2376_ = v___x_2359_;
goto v_reusejp_2375_;
}
else
{
lean_object* v_reuseFailAlloc_2377_; 
v_reuseFailAlloc_2377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2377_, 0, v___x_2374_);
lean_ctor_set(v_reuseFailAlloc_2377_, 1, v_a_2357_);
v___x_2376_ = v_reuseFailAlloc_2377_;
goto v_reusejp_2375_;
}
v_reusejp_2375_:
{
return v___x_2376_;
}
}
}
}
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertFormatPart___closed__1(void){
_start:
{
lean_object* v___x_2380_; lean_object* v___x_2381_; 
v___x_2380_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertFormatPart___closed__0));
v___x_2381_ = l_String_toRawSubstring_x27(v___x_2380_);
return v___x_2381_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertFormatPart___closed__4(void){
_start:
{
lean_object* v___x_2385_; lean_object* v___x_2386_; 
v___x_2385_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertFormatPart___closed__3));
v___x_2386_ = l_String_toRawSubstring_x27(v___x_2385_);
return v___x_2386_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertFormatPart(lean_object* v_x_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_){
_start:
{
if (lean_obj_tag(v_x_2389_) == 0)
{
lean_object* v_val_2392_; lean_object* v_quotContext_2393_; lean_object* v_currMacroScope_2394_; lean_object* v_ref_2395_; uint8_t v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; 
v_val_2392_ = lean_ctor_get(v_x_2389_, 0);
lean_inc_ref(v_val_2392_);
lean_dec_ref(v_x_2389_);
v_quotContext_2393_ = lean_ctor_get(v_a_2390_, 1);
lean_inc(v_quotContext_2393_);
v_currMacroScope_2394_ = lean_ctor_get(v_a_2390_, 2);
lean_inc(v_currMacroScope_2394_);
v_ref_2395_ = lean_ctor_get(v_a_2390_, 5);
lean_inc(v_ref_2395_);
lean_dec_ref(v_a_2390_);
v___x_2396_ = 0;
v___x_2397_ = l_Lean_SourceInfo_fromRef(v_ref_2395_, v___x_2396_);
lean_dec(v_ref_2395_);
v___x_2398_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2399_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__67));
v___x_2400_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__68));
lean_inc(v___x_2397_);
v___x_2401_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2401_, 0, v___x_2397_);
lean_ctor_set(v___x_2401_, 1, v___x_2400_);
v___x_2402_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertFormatPart___closed__1, &l___private_Std_Time_Notation_0__Std_Time_convertFormatPart___closed__1_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertFormatPart___closed__1);
v___x_2403_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertFormatPart___closed__2));
v___x_2404_ = l_Lean_addMacroScope(v_quotContext_2393_, v___x_2403_, v_currMacroScope_2394_);
v___x_2405_ = lean_box(0);
lean_inc(v___x_2397_);
v___x_2406_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2406_, 0, v___x_2397_);
lean_ctor_set(v___x_2406_, 1, v___x_2402_);
lean_ctor_set(v___x_2406_, 2, v___x_2404_);
lean_ctor_set(v___x_2406_, 3, v___x_2405_);
lean_inc(v___x_2397_);
v___x_2407_ = l_Lean_Syntax_node2(v___x_2397_, v___x_2399_, v___x_2401_, v___x_2406_);
v___x_2408_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2409_ = lean_box(2);
v___x_2410_ = l_Lean_Syntax_mkStrLit(v_val_2392_, v___x_2409_);
lean_inc(v___x_2397_);
v___x_2411_ = l_Lean_Syntax_node1(v___x_2397_, v___x_2408_, v___x_2410_);
v___x_2412_ = l_Lean_Syntax_node2(v___x_2397_, v___x_2398_, v___x_2407_, v___x_2411_);
v___x_2413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2413_, 0, v___x_2412_);
lean_ctor_set(v___x_2413_, 1, v_a_2391_);
return v___x_2413_;
}
else
{
lean_object* v_modifier_2414_; lean_object* v___x_2415_; lean_object* v_a_2416_; lean_object* v_a_2417_; lean_object* v___x_2419_; uint8_t v_isShared_2420_; uint8_t v_isSharedCheck_2442_; 
v_modifier_2414_ = lean_ctor_get(v_x_2389_, 0);
lean_inc(v_modifier_2414_);
lean_dec_ref(v_x_2389_);
lean_inc_ref(v_a_2390_);
v___x_2415_ = l___private_Std_Time_Notation_0__Std_Time_convertModifier(v_modifier_2414_, v_a_2390_, v_a_2391_);
v_a_2416_ = lean_ctor_get(v___x_2415_, 0);
v_a_2417_ = lean_ctor_get(v___x_2415_, 1);
v_isSharedCheck_2442_ = !lean_is_exclusive(v___x_2415_);
if (v_isSharedCheck_2442_ == 0)
{
v___x_2419_ = v___x_2415_;
v_isShared_2420_ = v_isSharedCheck_2442_;
goto v_resetjp_2418_;
}
else
{
lean_inc(v_a_2417_);
lean_inc(v_a_2416_);
lean_dec(v___x_2415_);
v___x_2419_ = lean_box(0);
v_isShared_2420_ = v_isSharedCheck_2442_;
goto v_resetjp_2418_;
}
v_resetjp_2418_:
{
lean_object* v_quotContext_2421_; lean_object* v_currMacroScope_2422_; lean_object* v_ref_2423_; uint8_t v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2440_; 
v_quotContext_2421_ = lean_ctor_get(v_a_2390_, 1);
lean_inc(v_quotContext_2421_);
v_currMacroScope_2422_ = lean_ctor_get(v_a_2390_, 2);
lean_inc(v_currMacroScope_2422_);
v_ref_2423_ = lean_ctor_get(v_a_2390_, 5);
lean_inc(v_ref_2423_);
lean_dec_ref(v_a_2390_);
v___x_2424_ = 0;
v___x_2425_ = l_Lean_SourceInfo_fromRef(v_ref_2423_, v___x_2424_);
lean_dec(v_ref_2423_);
v___x_2426_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2427_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__67));
v___x_2428_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__68));
lean_inc(v___x_2425_);
v___x_2429_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2429_, 0, v___x_2425_);
lean_ctor_set(v___x_2429_, 1, v___x_2428_);
v___x_2430_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertFormatPart___closed__4, &l___private_Std_Time_Notation_0__Std_Time_convertFormatPart___closed__4_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertFormatPart___closed__4);
v___x_2431_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertFormatPart___closed__5));
v___x_2432_ = l_Lean_addMacroScope(v_quotContext_2421_, v___x_2431_, v_currMacroScope_2422_);
v___x_2433_ = lean_box(0);
lean_inc(v___x_2425_);
v___x_2434_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2434_, 0, v___x_2425_);
lean_ctor_set(v___x_2434_, 1, v___x_2430_);
lean_ctor_set(v___x_2434_, 2, v___x_2432_);
lean_ctor_set(v___x_2434_, 3, v___x_2433_);
lean_inc(v___x_2425_);
v___x_2435_ = l_Lean_Syntax_node2(v___x_2425_, v___x_2427_, v___x_2429_, v___x_2434_);
v___x_2436_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
lean_inc(v___x_2425_);
v___x_2437_ = l_Lean_Syntax_node1(v___x_2425_, v___x_2436_, v_a_2416_);
v___x_2438_ = l_Lean_Syntax_node2(v___x_2425_, v___x_2426_, v___x_2435_, v___x_2437_);
if (v_isShared_2420_ == 0)
{
lean_ctor_set(v___x_2419_, 0, v___x_2438_);
v___x_2440_ = v___x_2419_;
goto v_reusejp_2439_;
}
else
{
lean_object* v_reuseFailAlloc_2441_; 
v_reuseFailAlloc_2441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2441_, 0, v___x_2438_);
lean_ctor_set(v_reuseFailAlloc_2441_, 1, v_a_2417_);
v___x_2440_ = v_reuseFailAlloc_2441_;
goto v_reusejp_2439_;
}
v_reusejp_2439_:
{
return v___x_2440_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxNat(lean_object* v_n_2446_, lean_object* v_a_2447_, lean_object* v_a_2448_){
_start:
{
lean_object* v_ref_2449_; uint8_t v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; 
v_ref_2449_ = lean_ctor_get(v_a_2447_, 5);
v___x_2450_ = 0;
v___x_2451_ = l_Lean_SourceInfo_fromRef(v_ref_2449_, v___x_2450_);
v___x_2452_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxNat___closed__1));
v___x_2453_ = l_Nat_reprFast(v_n_2446_);
lean_inc(v___x_2451_);
v___x_2454_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2454_, 0, v___x_2451_);
lean_ctor_set(v___x_2454_, 1, v___x_2453_);
v___x_2455_ = l_Lean_Syntax_node1(v___x_2451_, v___x_2452_, v___x_2454_);
v___x_2456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2456_, 0, v___x_2455_);
lean_ctor_set(v___x_2456_, 1, v_a_2448_);
return v___x_2456_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxNat___boxed(lean_object* v_n_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_){
_start:
{
lean_object* v_res_2460_; 
v_res_2460_ = l___private_Std_Time_Notation_0__Std_Time_syntaxNat(v_n_2457_, v_a_2458_, v_a_2459_);
lean_dec_ref(v_a_2458_);
return v_res_2460_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxString(lean_object* v_n_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_){
_start:
{
lean_object* v_ref_2467_; uint8_t v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; 
v_ref_2467_ = lean_ctor_get(v_a_2465_, 5);
v___x_2468_ = 0;
v___x_2469_ = l_Lean_SourceInfo_fromRef(v_ref_2467_, v___x_2468_);
v___x_2470_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxString___closed__1));
lean_inc(v___x_2469_);
v___x_2471_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2471_, 0, v___x_2469_);
lean_ctor_set(v___x_2471_, 1, v_n_2464_);
v___x_2472_ = l_Lean_Syntax_node1(v___x_2469_, v___x_2470_, v___x_2471_);
v___x_2473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2473_, 0, v___x_2472_);
lean_ctor_set(v___x_2473_, 1, v_a_2466_);
return v___x_2473_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxString___boxed(lean_object* v_n_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_){
_start:
{
lean_object* v_res_2477_; 
v_res_2477_ = l___private_Std_Time_Notation_0__Std_Time_syntaxString(v_n_2474_, v_a_2475_, v_a_2476_);
lean_dec_ref(v_a_2475_);
return v_res_2477_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__0(void){
_start:
{
lean_object* v_natZero_2478_; lean_object* v_intZero_2479_; 
v_natZero_2478_ = lean_unsigned_to_nat(0u);
v_intZero_2479_ = lean_nat_to_int(v_natZero_2478_);
return v_intZero_2479_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__2(void){
_start:
{
lean_object* v___x_2481_; lean_object* v___x_2482_; 
v___x_2481_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__1));
v___x_2482_ = l_String_toRawSubstring_x27(v___x_2481_);
return v___x_2482_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__11(void){
_start:
{
lean_object* v___x_2500_; lean_object* v___x_2501_; 
v___x_2500_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__10));
v___x_2501_ = l_String_toRawSubstring_x27(v___x_2500_);
return v___x_2501_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxInt(lean_object* v_n_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_){
_start:
{
lean_object* v_intZero_2520_; uint8_t v_isNeg_2521_; 
v_intZero_2520_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__0, &l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__0_once, _init_l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__0);
v_isNeg_2521_ = lean_int_dec_lt(v_n_2517_, v_intZero_2520_);
if (v_isNeg_2521_ == 0)
{
lean_object* v_quotContext_2522_; lean_object* v_currMacroScope_2523_; lean_object* v_ref_2524_; lean_object* v_a_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; 
v_quotContext_2522_ = lean_ctor_get(v_a_2518_, 1);
lean_inc(v_quotContext_2522_);
v_currMacroScope_2523_ = lean_ctor_get(v_a_2518_, 2);
lean_inc(v_currMacroScope_2523_);
v_ref_2524_ = lean_ctor_get(v_a_2518_, 5);
lean_inc(v_ref_2524_);
lean_dec_ref(v_a_2518_);
v_a_2525_ = lean_nat_abs(v_n_2517_);
v___x_2526_ = l_Lean_SourceInfo_fromRef(v_ref_2524_, v_isNeg_2521_);
lean_dec(v_ref_2524_);
v___x_2527_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2528_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__2, &l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__2_once, _init_l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__2);
v___x_2529_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__5));
v___x_2530_ = l_Lean_addMacroScope(v_quotContext_2522_, v___x_2529_, v_currMacroScope_2523_);
v___x_2531_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__9));
lean_inc(v___x_2526_);
v___x_2532_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2532_, 0, v___x_2526_);
lean_ctor_set(v___x_2532_, 1, v___x_2528_);
lean_ctor_set(v___x_2532_, 2, v___x_2530_);
lean_ctor_set(v___x_2532_, 3, v___x_2531_);
v___x_2533_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2534_ = l_Nat_reprFast(v_a_2525_);
v___x_2535_ = lean_box(2);
v___x_2536_ = l_Lean_Syntax_mkNumLit(v___x_2534_, v___x_2535_);
lean_inc(v___x_2526_);
v___x_2537_ = l_Lean_Syntax_node1(v___x_2526_, v___x_2533_, v___x_2536_);
v___x_2538_ = l_Lean_Syntax_node2(v___x_2526_, v___x_2527_, v___x_2532_, v___x_2537_);
v___x_2539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2539_, 0, v___x_2538_);
lean_ctor_set(v___x_2539_, 1, v_a_2519_);
return v___x_2539_;
}
else
{
lean_object* v_quotContext_2540_; lean_object* v_currMacroScope_2541_; lean_object* v_ref_2542_; lean_object* v_abs_2543_; lean_object* v_one_2544_; lean_object* v_a_2545_; uint8_t v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; 
v_quotContext_2540_ = lean_ctor_get(v_a_2518_, 1);
lean_inc(v_quotContext_2540_);
v_currMacroScope_2541_ = lean_ctor_get(v_a_2518_, 2);
lean_inc(v_currMacroScope_2541_);
v_ref_2542_ = lean_ctor_get(v_a_2518_, 5);
lean_inc(v_ref_2542_);
lean_dec_ref(v_a_2518_);
v_abs_2543_ = lean_nat_abs(v_n_2517_);
v_one_2544_ = lean_unsigned_to_nat(1u);
v_a_2545_ = lean_nat_sub(v_abs_2543_, v_one_2544_);
lean_dec(v_abs_2543_);
v___x_2546_ = 0;
v___x_2547_ = l_Lean_SourceInfo_fromRef(v_ref_2542_, v___x_2546_);
lean_dec(v_ref_2542_);
v___x_2548_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2549_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__11, &l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__11_once, _init_l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__11);
v___x_2550_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__13));
v___x_2551_ = l_Lean_addMacroScope(v_quotContext_2540_, v___x_2550_, v_currMacroScope_2541_);
v___x_2552_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__17));
lean_inc(v___x_2547_);
v___x_2553_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2553_, 0, v___x_2547_);
lean_ctor_set(v___x_2553_, 1, v___x_2549_);
lean_ctor_set(v___x_2553_, 2, v___x_2551_);
lean_ctor_set(v___x_2553_, 3, v___x_2552_);
v___x_2554_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2555_ = l_Nat_reprFast(v_a_2545_);
v___x_2556_ = lean_box(2);
v___x_2557_ = l_Lean_Syntax_mkNumLit(v___x_2555_, v___x_2556_);
lean_inc(v___x_2547_);
v___x_2558_ = l_Lean_Syntax_node1(v___x_2547_, v___x_2554_, v___x_2557_);
v___x_2559_ = l_Lean_Syntax_node2(v___x_2547_, v___x_2548_, v___x_2553_, v___x_2558_);
v___x_2560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2560_, 0, v___x_2559_);
lean_ctor_set(v___x_2560_, 1, v_a_2519_);
return v___x_2560_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxInt___boxed(lean_object* v_n_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_){
_start:
{
lean_object* v_res_2564_; 
v_res_2564_ = l___private_Std_Time_Notation_0__Std_Time_syntaxInt(v_n_2561_, v_a_2562_, v_a_2563_);
lean_dec(v_n_2561_);
return v_res_2564_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__1(void){
_start:
{
lean_object* v___x_2566_; lean_object* v___x_2567_; 
v___x_2566_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__0));
v___x_2567_ = l_String_toRawSubstring_x27(v___x_2566_);
return v___x_2567_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__21(void){
_start:
{
lean_object* v___x_2617_; 
v___x_2617_ = l_Array_mkArray0(lean_box(0));
return v___x_2617_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxBounded(lean_object* v_n_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_){
_start:
{
lean_object* v___x_2621_; lean_object* v_a_2622_; lean_object* v_a_2623_; lean_object* v___x_2625_; uint8_t v_isShared_2626_; uint8_t v_isSharedCheck_2676_; 
lean_inc_ref(v_a_2619_);
v___x_2621_ = l___private_Std_Time_Notation_0__Std_Time_syntaxInt(v_n_2618_, v_a_2619_, v_a_2620_);
v_a_2622_ = lean_ctor_get(v___x_2621_, 0);
v_a_2623_ = lean_ctor_get(v___x_2621_, 1);
v_isSharedCheck_2676_ = !lean_is_exclusive(v___x_2621_);
if (v_isSharedCheck_2676_ == 0)
{
v___x_2625_ = v___x_2621_;
v_isShared_2626_ = v_isSharedCheck_2676_;
goto v_resetjp_2624_;
}
else
{
lean_inc(v_a_2623_);
lean_inc(v_a_2622_);
lean_dec(v___x_2621_);
v___x_2625_ = lean_box(0);
v_isShared_2626_ = v_isSharedCheck_2676_;
goto v_resetjp_2624_;
}
v_resetjp_2624_:
{
lean_object* v_quotContext_2627_; lean_object* v_currMacroScope_2628_; lean_object* v_ref_2629_; uint8_t v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2674_; 
v_quotContext_2627_ = lean_ctor_get(v_a_2619_, 1);
lean_inc(v_quotContext_2627_);
v_currMacroScope_2628_ = lean_ctor_get(v_a_2619_, 2);
lean_inc(v_currMacroScope_2628_);
v_ref_2629_ = lean_ctor_get(v_a_2619_, 5);
lean_inc(v_ref_2629_);
lean_dec_ref(v_a_2619_);
v___x_2630_ = 0;
v___x_2631_ = l_Lean_SourceInfo_fromRef(v_ref_2629_, v___x_2630_);
lean_dec(v_ref_2629_);
v___x_2632_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2633_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__1, &l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__1_once, _init_l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__1);
v___x_2634_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__6));
lean_inc(v_currMacroScope_2628_);
lean_inc(v_quotContext_2627_);
v___x_2635_ = l_Lean_addMacroScope(v_quotContext_2627_, v___x_2634_, v_currMacroScope_2628_);
v___x_2636_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__8));
lean_inc(v___x_2631_);
v___x_2637_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2637_, 0, v___x_2631_);
lean_ctor_set(v___x_2637_, 1, v___x_2633_);
lean_ctor_set(v___x_2637_, 2, v___x_2635_);
lean_ctor_set(v___x_2637_, 3, v___x_2636_);
v___x_2638_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2639_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__42));
v___x_2640_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__44));
v___x_2641_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__45));
lean_inc(v___x_2631_);
v___x_2642_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2642_, 0, v___x_2631_);
lean_ctor_set(v___x_2642_, 1, v___x_2641_);
v___x_2643_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__47));
v___x_2644_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49);
v___x_2645_ = lean_box(0);
v___x_2646_ = l_Lean_addMacroScope(v_quotContext_2627_, v___x_2645_, v_currMacroScope_2628_);
v___x_2647_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__65));
lean_inc(v___x_2631_);
v___x_2648_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2648_, 0, v___x_2631_);
lean_ctor_set(v___x_2648_, 1, v___x_2644_);
lean_ctor_set(v___x_2648_, 2, v___x_2646_);
lean_ctor_set(v___x_2648_, 3, v___x_2647_);
lean_inc(v___x_2631_);
v___x_2649_ = l_Lean_Syntax_node1(v___x_2631_, v___x_2643_, v___x_2648_);
lean_inc(v___x_2631_);
v___x_2650_ = l_Lean_Syntax_node2(v___x_2631_, v___x_2640_, v___x_2642_, v___x_2649_);
v___x_2651_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__10));
v___x_2652_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__11));
lean_inc(v___x_2631_);
v___x_2653_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2653_, 0, v___x_2631_);
lean_ctor_set(v___x_2653_, 1, v___x_2652_);
v___x_2654_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__14));
v___x_2655_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__16));
v___x_2656_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__17));
v___x_2657_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__18));
lean_inc(v___x_2631_);
v___x_2658_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2658_, 0, v___x_2631_);
lean_ctor_set(v___x_2658_, 1, v___x_2656_);
v___x_2659_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__20));
v___x_2660_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__21, &l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__21_once, _init_l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__21);
lean_inc(v___x_2631_);
v___x_2661_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2661_, 0, v___x_2631_);
lean_ctor_set(v___x_2661_, 1, v___x_2638_);
lean_ctor_set(v___x_2661_, 2, v___x_2660_);
lean_inc(v___x_2631_);
v___x_2662_ = l_Lean_Syntax_node1(v___x_2631_, v___x_2659_, v___x_2661_);
lean_inc(v___x_2631_);
v___x_2663_ = l_Lean_Syntax_node2(v___x_2631_, v___x_2657_, v___x_2658_, v___x_2662_);
lean_inc(v___x_2631_);
v___x_2664_ = l_Lean_Syntax_node1(v___x_2631_, v___x_2638_, v___x_2663_);
lean_inc(v___x_2631_);
v___x_2665_ = l_Lean_Syntax_node1(v___x_2631_, v___x_2655_, v___x_2664_);
lean_inc(v___x_2631_);
v___x_2666_ = l_Lean_Syntax_node1(v___x_2631_, v___x_2654_, v___x_2665_);
lean_inc(v___x_2631_);
v___x_2667_ = l_Lean_Syntax_node2(v___x_2631_, v___x_2651_, v___x_2653_, v___x_2666_);
v___x_2668_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__72));
lean_inc(v___x_2631_);
v___x_2669_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2669_, 0, v___x_2631_);
lean_ctor_set(v___x_2669_, 1, v___x_2668_);
lean_inc(v___x_2631_);
v___x_2670_ = l_Lean_Syntax_node3(v___x_2631_, v___x_2639_, v___x_2650_, v___x_2667_, v___x_2669_);
lean_inc(v___x_2631_);
v___x_2671_ = l_Lean_Syntax_node2(v___x_2631_, v___x_2638_, v_a_2622_, v___x_2670_);
v___x_2672_ = l_Lean_Syntax_node2(v___x_2631_, v___x_2632_, v___x_2637_, v___x_2671_);
if (v_isShared_2626_ == 0)
{
lean_ctor_set(v___x_2625_, 0, v___x_2672_);
v___x_2674_ = v___x_2625_;
goto v_reusejp_2673_;
}
else
{
lean_object* v_reuseFailAlloc_2675_; 
v_reuseFailAlloc_2675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2675_, 0, v___x_2672_);
lean_ctor_set(v_reuseFailAlloc_2675_, 1, v_a_2623_);
v___x_2674_ = v_reuseFailAlloc_2675_;
goto v_reusejp_2673_;
}
v_reusejp_2673_:
{
return v___x_2674_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___boxed(lean_object* v_n_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_){
_start:
{
lean_object* v_res_2680_; 
v_res_2680_ = l___private_Std_Time_Notation_0__Std_Time_syntaxBounded(v_n_2677_, v_a_2678_, v_a_2679_);
lean_dec(v_n_2677_);
return v_res_2680_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_syntaxVal___closed__1(void){
_start:
{
lean_object* v___x_2682_; lean_object* v___x_2683_; 
v___x_2682_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxVal___closed__0));
v___x_2683_ = l_String_toRawSubstring_x27(v___x_2682_);
return v___x_2683_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxVal(lean_object* v_n_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_){
_start:
{
lean_object* v___x_2706_; lean_object* v_a_2707_; lean_object* v_a_2708_; lean_object* v___x_2710_; uint8_t v_isShared_2711_; uint8_t v_isSharedCheck_2729_; 
lean_inc_ref(v_a_2704_);
v___x_2706_ = l___private_Std_Time_Notation_0__Std_Time_syntaxInt(v_n_2703_, v_a_2704_, v_a_2705_);
v_a_2707_ = lean_ctor_get(v___x_2706_, 0);
v_a_2708_ = lean_ctor_get(v___x_2706_, 1);
v_isSharedCheck_2729_ = !lean_is_exclusive(v___x_2706_);
if (v_isSharedCheck_2729_ == 0)
{
v___x_2710_ = v___x_2706_;
v_isShared_2711_ = v_isSharedCheck_2729_;
goto v_resetjp_2709_;
}
else
{
lean_inc(v_a_2708_);
lean_inc(v_a_2707_);
lean_dec(v___x_2706_);
v___x_2710_ = lean_box(0);
v_isShared_2711_ = v_isSharedCheck_2729_;
goto v_resetjp_2709_;
}
v_resetjp_2709_:
{
lean_object* v_quotContext_2712_; lean_object* v_currMacroScope_2713_; lean_object* v_ref_2714_; uint8_t v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2727_; 
v_quotContext_2712_ = lean_ctor_get(v_a_2704_, 1);
lean_inc(v_quotContext_2712_);
v_currMacroScope_2713_ = lean_ctor_get(v_a_2704_, 2);
lean_inc(v_currMacroScope_2713_);
v_ref_2714_ = lean_ctor_get(v_a_2704_, 5);
lean_inc(v_ref_2714_);
lean_dec_ref(v_a_2704_);
v___x_2715_ = 0;
v___x_2716_ = l_Lean_SourceInfo_fromRef(v_ref_2714_, v___x_2715_);
lean_dec(v_ref_2714_);
v___x_2717_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2718_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_syntaxVal___closed__1, &l___private_Std_Time_Notation_0__Std_Time_syntaxVal___closed__1_once, _init_l___private_Std_Time_Notation_0__Std_Time_syntaxVal___closed__1);
v___x_2719_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxVal___closed__4));
v___x_2720_ = l_Lean_addMacroScope(v_quotContext_2712_, v___x_2719_, v_currMacroScope_2713_);
v___x_2721_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxVal___closed__8));
lean_inc(v___x_2716_);
v___x_2722_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2722_, 0, v___x_2716_);
lean_ctor_set(v___x_2722_, 1, v___x_2718_);
lean_ctor_set(v___x_2722_, 2, v___x_2720_);
lean_ctor_set(v___x_2722_, 3, v___x_2721_);
v___x_2723_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
lean_inc(v___x_2716_);
v___x_2724_ = l_Lean_Syntax_node1(v___x_2716_, v___x_2723_, v_a_2707_);
v___x_2725_ = l_Lean_Syntax_node2(v___x_2716_, v___x_2717_, v___x_2722_, v___x_2724_);
if (v_isShared_2711_ == 0)
{
lean_ctor_set(v___x_2710_, 0, v___x_2725_);
v___x_2727_ = v___x_2710_;
goto v_reusejp_2726_;
}
else
{
lean_object* v_reuseFailAlloc_2728_; 
v_reuseFailAlloc_2728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2728_, 0, v___x_2725_);
lean_ctor_set(v_reuseFailAlloc_2728_, 1, v_a_2708_);
v___x_2727_ = v_reuseFailAlloc_2728_;
goto v_reusejp_2726_;
}
v_reusejp_2726_:
{
return v___x_2727_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxVal___boxed(lean_object* v_n_2730_, lean_object* v_a_2731_, lean_object* v_a_2732_){
_start:
{
lean_object* v_res_2733_; 
v_res_2733_ = l___private_Std_Time_Notation_0__Std_Time_syntaxVal(v_n_2730_, v_a_2731_, v_a_2732_);
lean_dec(v_n_2730_);
return v_res_2733_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertOffset___closed__1(void){
_start:
{
lean_object* v___x_2735_; lean_object* v___x_2736_; 
v___x_2735_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffset___closed__0));
v___x_2736_ = l_String_toRawSubstring_x27(v___x_2735_);
return v___x_2736_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffset(lean_object* v_offset_2757_, lean_object* v_a_2758_, lean_object* v_a_2759_){
_start:
{
lean_object* v___x_2760_; lean_object* v_a_2761_; lean_object* v_a_2762_; lean_object* v___x_2764_; uint8_t v_isShared_2765_; uint8_t v_isSharedCheck_2783_; 
lean_inc_ref(v_a_2758_);
v___x_2760_ = l___private_Std_Time_Notation_0__Std_Time_syntaxVal(v_offset_2757_, v_a_2758_, v_a_2759_);
v_a_2761_ = lean_ctor_get(v___x_2760_, 0);
v_a_2762_ = lean_ctor_get(v___x_2760_, 1);
v_isSharedCheck_2783_ = !lean_is_exclusive(v___x_2760_);
if (v_isSharedCheck_2783_ == 0)
{
v___x_2764_ = v___x_2760_;
v_isShared_2765_ = v_isSharedCheck_2783_;
goto v_resetjp_2763_;
}
else
{
lean_inc(v_a_2762_);
lean_inc(v_a_2761_);
lean_dec(v___x_2760_);
v___x_2764_ = lean_box(0);
v_isShared_2765_ = v_isSharedCheck_2783_;
goto v_resetjp_2763_;
}
v_resetjp_2763_:
{
lean_object* v_quotContext_2766_; lean_object* v_currMacroScope_2767_; lean_object* v_ref_2768_; uint8_t v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2781_; 
v_quotContext_2766_ = lean_ctor_get(v_a_2758_, 1);
lean_inc(v_quotContext_2766_);
v_currMacroScope_2767_ = lean_ctor_get(v_a_2758_, 2);
lean_inc(v_currMacroScope_2767_);
v_ref_2768_ = lean_ctor_get(v_a_2758_, 5);
lean_inc(v_ref_2768_);
lean_dec_ref(v_a_2758_);
v___x_2769_ = 0;
v___x_2770_ = l_Lean_SourceInfo_fromRef(v_ref_2768_, v___x_2769_);
lean_dec(v_ref_2768_);
v___x_2771_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2772_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertOffset___closed__1, &l___private_Std_Time_Notation_0__Std_Time_convertOffset___closed__1_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertOffset___closed__1);
v___x_2773_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffset___closed__5));
v___x_2774_ = l_Lean_addMacroScope(v_quotContext_2766_, v___x_2773_, v_currMacroScope_2767_);
v___x_2775_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffset___closed__9));
lean_inc(v___x_2770_);
v___x_2776_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2776_, 0, v___x_2770_);
lean_ctor_set(v___x_2776_, 1, v___x_2772_);
lean_ctor_set(v___x_2776_, 2, v___x_2774_);
lean_ctor_set(v___x_2776_, 3, v___x_2775_);
v___x_2777_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
lean_inc(v___x_2770_);
v___x_2778_ = l_Lean_Syntax_node1(v___x_2770_, v___x_2777_, v_a_2761_);
v___x_2779_ = l_Lean_Syntax_node2(v___x_2770_, v___x_2771_, v___x_2776_, v___x_2778_);
if (v_isShared_2765_ == 0)
{
lean_ctor_set(v___x_2764_, 0, v___x_2779_);
v___x_2781_ = v___x_2764_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2782_; 
v_reuseFailAlloc_2782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2782_, 0, v___x_2779_);
lean_ctor_set(v_reuseFailAlloc_2782_, 1, v_a_2762_);
v___x_2781_ = v_reuseFailAlloc_2782_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
return v___x_2781_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffset___boxed(lean_object* v_offset_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_){
_start:
{
lean_object* v_res_2787_; 
v_res_2787_ = l___private_Std_Time_Notation_0__Std_Time_convertOffset(v_offset_2784_, v_a_2785_, v_a_2786_);
lean_dec(v_offset_2784_);
return v_res_2787_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__1(void){
_start:
{
lean_object* v___x_2789_; lean_object* v___x_2790_; 
v___x_2789_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__0));
v___x_2790_ = l_String_toRawSubstring_x27(v___x_2789_);
return v___x_2790_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__8(void){
_start:
{
lean_object* v___x_2808_; lean_object* v___x_2809_; 
v___x_2808_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__7));
v___x_2809_ = l_String_toRawSubstring_x27(v___x_2808_);
return v___x_2809_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertTimezone(lean_object* v_tz_2822_, lean_object* v_a_2823_, lean_object* v_a_2824_){
_start:
{
lean_object* v_offset_2825_; lean_object* v_name_2826_; lean_object* v_abbreviation_2827_; lean_object* v___x_2828_; lean_object* v_a_2829_; lean_object* v_a_2830_; lean_object* v___x_2832_; uint8_t v_isShared_2833_; uint8_t v_isSharedCheck_2859_; 
v_offset_2825_ = lean_ctor_get(v_tz_2822_, 0);
lean_inc(v_offset_2825_);
v_name_2826_ = lean_ctor_get(v_tz_2822_, 1);
lean_inc_ref(v_name_2826_);
v_abbreviation_2827_ = lean_ctor_get(v_tz_2822_, 2);
lean_inc_ref(v_abbreviation_2827_);
lean_dec_ref(v_tz_2822_);
lean_inc_ref(v_a_2823_);
v___x_2828_ = l___private_Std_Time_Notation_0__Std_Time_convertOffset(v_offset_2825_, v_a_2823_, v_a_2824_);
lean_dec(v_offset_2825_);
v_a_2829_ = lean_ctor_get(v___x_2828_, 0);
v_a_2830_ = lean_ctor_get(v___x_2828_, 1);
v_isSharedCheck_2859_ = !lean_is_exclusive(v___x_2828_);
if (v_isSharedCheck_2859_ == 0)
{
v___x_2832_ = v___x_2828_;
v_isShared_2833_ = v_isSharedCheck_2859_;
goto v_resetjp_2831_;
}
else
{
lean_inc(v_a_2830_);
lean_inc(v_a_2829_);
lean_dec(v___x_2828_);
v___x_2832_ = lean_box(0);
v_isShared_2833_ = v_isSharedCheck_2859_;
goto v_resetjp_2831_;
}
v_resetjp_2831_:
{
lean_object* v_quotContext_2834_; lean_object* v_currMacroScope_2835_; lean_object* v_ref_2836_; uint8_t v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2857_; 
v_quotContext_2834_ = lean_ctor_get(v_a_2823_, 1);
lean_inc(v_quotContext_2834_);
v_currMacroScope_2835_ = lean_ctor_get(v_a_2823_, 2);
lean_inc(v_currMacroScope_2835_);
v_ref_2836_ = lean_ctor_get(v_a_2823_, 5);
lean_inc(v_ref_2836_);
lean_dec_ref(v_a_2823_);
v___x_2837_ = 0;
v___x_2838_ = l_Lean_SourceInfo_fromRef(v_ref_2836_, v___x_2837_);
lean_dec(v_ref_2836_);
v___x_2839_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2840_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__1, &l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__1_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__1);
v___x_2841_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__2));
lean_inc(v_currMacroScope_2835_);
lean_inc(v_quotContext_2834_);
v___x_2842_ = l_Lean_addMacroScope(v_quotContext_2834_, v___x_2841_, v_currMacroScope_2835_);
v___x_2843_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__6));
lean_inc(v___x_2838_);
v___x_2844_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2844_, 0, v___x_2838_);
lean_ctor_set(v___x_2844_, 1, v___x_2840_);
lean_ctor_set(v___x_2844_, 2, v___x_2842_);
lean_ctor_set(v___x_2844_, 3, v___x_2843_);
v___x_2845_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2846_ = lean_box(2);
v___x_2847_ = l_Lean_Syntax_mkStrLit(v_name_2826_, v___x_2846_);
v___x_2848_ = l_Lean_Syntax_mkStrLit(v_abbreviation_2827_, v___x_2846_);
v___x_2849_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__8, &l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__8_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__8);
v___x_2850_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__9));
v___x_2851_ = l_Lean_addMacroScope(v_quotContext_2834_, v___x_2850_, v_currMacroScope_2835_);
v___x_2852_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__13));
lean_inc(v___x_2838_);
v___x_2853_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2853_, 0, v___x_2838_);
lean_ctor_set(v___x_2853_, 1, v___x_2849_);
lean_ctor_set(v___x_2853_, 2, v___x_2851_);
lean_ctor_set(v___x_2853_, 3, v___x_2852_);
lean_inc(v___x_2838_);
v___x_2854_ = l_Lean_Syntax_node4(v___x_2838_, v___x_2845_, v_a_2829_, v___x_2847_, v___x_2848_, v___x_2853_);
v___x_2855_ = l_Lean_Syntax_node2(v___x_2838_, v___x_2839_, v___x_2844_, v___x_2854_);
if (v_isShared_2833_ == 0)
{
lean_ctor_set(v___x_2832_, 0, v___x_2855_);
v___x_2857_ = v___x_2832_;
goto v_reusejp_2856_;
}
else
{
lean_object* v_reuseFailAlloc_2858_; 
v_reuseFailAlloc_2858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2858_, 0, v___x_2855_);
lean_ctor_set(v_reuseFailAlloc_2858_, 1, v_a_2830_);
v___x_2857_ = v_reuseFailAlloc_2858_;
goto v_reusejp_2856_;
}
v_reusejp_2856_:
{
return v___x_2857_;
}
}
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertPlainDate___closed__1(void){
_start:
{
lean_object* v___x_2861_; lean_object* v___x_2862_; 
v___x_2861_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertPlainDate___closed__0));
v___x_2862_ = l_String_toRawSubstring_x27(v___x_2861_);
return v___x_2862_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertPlainDate(lean_object* v_d_2876_, lean_object* v_a_2877_, lean_object* v_a_2878_){
_start:
{
lean_object* v_year_2879_; lean_object* v_month_2880_; lean_object* v_day_2881_; lean_object* v___x_2882_; lean_object* v_a_2883_; lean_object* v_a_2884_; lean_object* v___x_2885_; lean_object* v_a_2886_; lean_object* v_a_2887_; lean_object* v___x_2888_; lean_object* v_a_2889_; lean_object* v_a_2890_; lean_object* v___x_2892_; uint8_t v_isShared_2893_; uint8_t v_isSharedCheck_2911_; 
v_year_2879_ = lean_ctor_get(v_d_2876_, 0);
v_month_2880_ = lean_ctor_get(v_d_2876_, 1);
v_day_2881_ = lean_ctor_get(v_d_2876_, 2);
lean_inc_ref(v_a_2877_);
v___x_2882_ = l___private_Std_Time_Notation_0__Std_Time_syntaxInt(v_year_2879_, v_a_2877_, v_a_2878_);
v_a_2883_ = lean_ctor_get(v___x_2882_, 0);
lean_inc(v_a_2883_);
v_a_2884_ = lean_ctor_get(v___x_2882_, 1);
lean_inc(v_a_2884_);
lean_dec_ref(v___x_2882_);
lean_inc_ref(v_a_2877_);
v___x_2885_ = l___private_Std_Time_Notation_0__Std_Time_syntaxBounded(v_month_2880_, v_a_2877_, v_a_2884_);
v_a_2886_ = lean_ctor_get(v___x_2885_, 0);
lean_inc(v_a_2886_);
v_a_2887_ = lean_ctor_get(v___x_2885_, 1);
lean_inc(v_a_2887_);
lean_dec_ref(v___x_2885_);
lean_inc_ref(v_a_2877_);
v___x_2888_ = l___private_Std_Time_Notation_0__Std_Time_syntaxBounded(v_day_2881_, v_a_2877_, v_a_2887_);
v_a_2889_ = lean_ctor_get(v___x_2888_, 0);
v_a_2890_ = lean_ctor_get(v___x_2888_, 1);
v_isSharedCheck_2911_ = !lean_is_exclusive(v___x_2888_);
if (v_isSharedCheck_2911_ == 0)
{
v___x_2892_ = v___x_2888_;
v_isShared_2893_ = v_isSharedCheck_2911_;
goto v_resetjp_2891_;
}
else
{
lean_inc(v_a_2890_);
lean_inc(v_a_2889_);
lean_dec(v___x_2888_);
v___x_2892_ = lean_box(0);
v_isShared_2893_ = v_isSharedCheck_2911_;
goto v_resetjp_2891_;
}
v_resetjp_2891_:
{
lean_object* v_quotContext_2894_; lean_object* v_currMacroScope_2895_; lean_object* v_ref_2896_; uint8_t v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2909_; 
v_quotContext_2894_ = lean_ctor_get(v_a_2877_, 1);
lean_inc(v_quotContext_2894_);
v_currMacroScope_2895_ = lean_ctor_get(v_a_2877_, 2);
lean_inc(v_currMacroScope_2895_);
v_ref_2896_ = lean_ctor_get(v_a_2877_, 5);
lean_inc(v_ref_2896_);
lean_dec_ref(v_a_2877_);
v___x_2897_ = 0;
v___x_2898_ = l_Lean_SourceInfo_fromRef(v_ref_2896_, v___x_2897_);
lean_dec(v_ref_2896_);
v___x_2899_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2900_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertPlainDate___closed__1, &l___private_Std_Time_Notation_0__Std_Time_convertPlainDate___closed__1_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertPlainDate___closed__1);
v___x_2901_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertPlainDate___closed__4));
v___x_2902_ = l_Lean_addMacroScope(v_quotContext_2894_, v___x_2901_, v_currMacroScope_2895_);
v___x_2903_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertPlainDate___closed__6));
lean_inc(v___x_2898_);
v___x_2904_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2904_, 0, v___x_2898_);
lean_ctor_set(v___x_2904_, 1, v___x_2900_);
lean_ctor_set(v___x_2904_, 2, v___x_2902_);
lean_ctor_set(v___x_2904_, 3, v___x_2903_);
v___x_2905_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
lean_inc(v___x_2898_);
v___x_2906_ = l_Lean_Syntax_node3(v___x_2898_, v___x_2905_, v_a_2883_, v_a_2886_, v_a_2889_);
v___x_2907_ = l_Lean_Syntax_node2(v___x_2898_, v___x_2899_, v___x_2904_, v___x_2906_);
if (v_isShared_2893_ == 0)
{
lean_ctor_set(v___x_2892_, 0, v___x_2907_);
v___x_2909_ = v___x_2892_;
goto v_reusejp_2908_;
}
else
{
lean_object* v_reuseFailAlloc_2910_; 
v_reuseFailAlloc_2910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2910_, 0, v___x_2907_);
lean_ctor_set(v_reuseFailAlloc_2910_, 1, v_a_2890_);
v___x_2909_ = v_reuseFailAlloc_2910_;
goto v_reusejp_2908_;
}
v_reusejp_2908_:
{
return v___x_2909_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertPlainDate___boxed(lean_object* v_d_2912_, lean_object* v_a_2913_, lean_object* v_a_2914_){
_start:
{
lean_object* v_res_2915_; 
v_res_2915_ = l___private_Std_Time_Notation_0__Std_Time_convertPlainDate(v_d_2912_, v_a_2913_, v_a_2914_);
lean_dec_ref(v_d_2912_);
return v_res_2915_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertPlainTime___closed__1(void){
_start:
{
lean_object* v___x_2917_; lean_object* v___x_2918_; 
v___x_2917_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertPlainTime___closed__0));
v___x_2918_ = l_String_toRawSubstring_x27(v___x_2917_);
return v___x_2918_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertPlainTime(lean_object* v_d_2936_, lean_object* v_a_2937_, lean_object* v_a_2938_){
_start:
{
lean_object* v_hour_2939_; lean_object* v_minute_2940_; lean_object* v_second_2941_; lean_object* v_nanosecond_2942_; lean_object* v___x_2944_; uint8_t v_isShared_2945_; uint8_t v_isSharedCheck_2981_; 
v_hour_2939_ = lean_ctor_get(v_d_2936_, 0);
v_minute_2940_ = lean_ctor_get(v_d_2936_, 1);
v_second_2941_ = lean_ctor_get(v_d_2936_, 2);
v_nanosecond_2942_ = lean_ctor_get(v_d_2936_, 3);
v_isSharedCheck_2981_ = !lean_is_exclusive(v_d_2936_);
if (v_isSharedCheck_2981_ == 0)
{
v___x_2944_ = v_d_2936_;
v_isShared_2945_ = v_isSharedCheck_2981_;
goto v_resetjp_2943_;
}
else
{
lean_inc(v_nanosecond_2942_);
lean_inc(v_second_2941_);
lean_inc(v_minute_2940_);
lean_inc(v_hour_2939_);
lean_dec(v_d_2936_);
v___x_2944_ = lean_box(0);
v_isShared_2945_ = v_isSharedCheck_2981_;
goto v_resetjp_2943_;
}
v_resetjp_2943_:
{
lean_object* v___x_2946_; lean_object* v_a_2947_; lean_object* v_a_2948_; lean_object* v___x_2949_; lean_object* v_a_2950_; lean_object* v_a_2951_; lean_object* v___x_2952_; lean_object* v_a_2953_; lean_object* v_a_2954_; lean_object* v___x_2955_; lean_object* v_a_2956_; lean_object* v_a_2957_; lean_object* v___x_2959_; uint8_t v_isShared_2960_; uint8_t v_isSharedCheck_2980_; 
lean_inc_ref(v_a_2937_);
v___x_2946_ = l___private_Std_Time_Notation_0__Std_Time_syntaxBounded(v_hour_2939_, v_a_2937_, v_a_2938_);
lean_dec(v_hour_2939_);
v_a_2947_ = lean_ctor_get(v___x_2946_, 0);
lean_inc(v_a_2947_);
v_a_2948_ = lean_ctor_get(v___x_2946_, 1);
lean_inc(v_a_2948_);
lean_dec_ref(v___x_2946_);
lean_inc_ref(v_a_2937_);
v___x_2949_ = l___private_Std_Time_Notation_0__Std_Time_syntaxBounded(v_minute_2940_, v_a_2937_, v_a_2948_);
lean_dec(v_minute_2940_);
v_a_2950_ = lean_ctor_get(v___x_2949_, 0);
lean_inc(v_a_2950_);
v_a_2951_ = lean_ctor_get(v___x_2949_, 1);
lean_inc(v_a_2951_);
lean_dec_ref(v___x_2949_);
lean_inc_ref(v_a_2937_);
v___x_2952_ = l___private_Std_Time_Notation_0__Std_Time_syntaxBounded(v_second_2941_, v_a_2937_, v_a_2951_);
lean_dec(v_second_2941_);
v_a_2953_ = lean_ctor_get(v___x_2952_, 0);
lean_inc(v_a_2953_);
v_a_2954_ = lean_ctor_get(v___x_2952_, 1);
lean_inc(v_a_2954_);
lean_dec_ref(v___x_2952_);
lean_inc_ref(v_a_2937_);
v___x_2955_ = l___private_Std_Time_Notation_0__Std_Time_syntaxBounded(v_nanosecond_2942_, v_a_2937_, v_a_2954_);
lean_dec(v_nanosecond_2942_);
v_a_2956_ = lean_ctor_get(v___x_2955_, 0);
v_a_2957_ = lean_ctor_get(v___x_2955_, 1);
v_isSharedCheck_2980_ = !lean_is_exclusive(v___x_2955_);
if (v_isSharedCheck_2980_ == 0)
{
v___x_2959_ = v___x_2955_;
v_isShared_2960_ = v_isSharedCheck_2980_;
goto v_resetjp_2958_;
}
else
{
lean_inc(v_a_2957_);
lean_inc(v_a_2956_);
lean_dec(v___x_2955_);
v___x_2959_ = lean_box(0);
v_isShared_2960_ = v_isSharedCheck_2980_;
goto v_resetjp_2958_;
}
v_resetjp_2958_:
{
lean_object* v_quotContext_2961_; lean_object* v_currMacroScope_2962_; lean_object* v_ref_2963_; uint8_t v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2972_; 
v_quotContext_2961_ = lean_ctor_get(v_a_2937_, 1);
lean_inc(v_quotContext_2961_);
v_currMacroScope_2962_ = lean_ctor_get(v_a_2937_, 2);
lean_inc(v_currMacroScope_2962_);
v_ref_2963_ = lean_ctor_get(v_a_2937_, 5);
lean_inc(v_ref_2963_);
lean_dec_ref(v_a_2937_);
v___x_2964_ = 0;
v___x_2965_ = l_Lean_SourceInfo_fromRef(v_ref_2963_, v___x_2964_);
lean_dec(v_ref_2963_);
v___x_2966_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2967_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertPlainTime___closed__1, &l___private_Std_Time_Notation_0__Std_Time_convertPlainTime___closed__1_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertPlainTime___closed__1);
v___x_2968_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertPlainTime___closed__3));
v___x_2969_ = l_Lean_addMacroScope(v_quotContext_2961_, v___x_2968_, v_currMacroScope_2962_);
v___x_2970_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertPlainTime___closed__7));
lean_inc(v___x_2965_);
if (v_isShared_2945_ == 0)
{
lean_ctor_set_tag(v___x_2944_, 3);
lean_ctor_set(v___x_2944_, 3, v___x_2970_);
lean_ctor_set(v___x_2944_, 2, v___x_2969_);
lean_ctor_set(v___x_2944_, 1, v___x_2967_);
lean_ctor_set(v___x_2944_, 0, v___x_2965_);
v___x_2972_ = v___x_2944_;
goto v_reusejp_2971_;
}
else
{
lean_object* v_reuseFailAlloc_2979_; 
v_reuseFailAlloc_2979_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2979_, 0, v___x_2965_);
lean_ctor_set(v_reuseFailAlloc_2979_, 1, v___x_2967_);
lean_ctor_set(v_reuseFailAlloc_2979_, 2, v___x_2969_);
lean_ctor_set(v_reuseFailAlloc_2979_, 3, v___x_2970_);
v___x_2972_ = v_reuseFailAlloc_2979_;
goto v_reusejp_2971_;
}
v_reusejp_2971_:
{
lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2977_; 
v___x_2973_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
lean_inc(v___x_2965_);
v___x_2974_ = l_Lean_Syntax_node4(v___x_2965_, v___x_2973_, v_a_2947_, v_a_2950_, v_a_2953_, v_a_2956_);
v___x_2975_ = l_Lean_Syntax_node2(v___x_2965_, v___x_2966_, v___x_2972_, v___x_2974_);
if (v_isShared_2960_ == 0)
{
lean_ctor_set(v___x_2959_, 0, v___x_2975_);
v___x_2977_ = v___x_2959_;
goto v_reusejp_2976_;
}
else
{
lean_object* v_reuseFailAlloc_2978_; 
v_reuseFailAlloc_2978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2978_, 0, v___x_2975_);
lean_ctor_set(v_reuseFailAlloc_2978_, 1, v_a_2957_);
v___x_2977_ = v_reuseFailAlloc_2978_;
goto v_reusejp_2976_;
}
v_reusejp_2976_:
{
return v___x_2977_;
}
}
}
}
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime___closed__1(void){
_start:
{
lean_object* v___x_2983_; lean_object* v___x_2984_; 
v___x_2983_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime___closed__0));
v___x_2984_ = l_String_toRawSubstring_x27(v___x_2983_);
return v___x_2984_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime(lean_object* v_d_3002_, lean_object* v_a_3003_, lean_object* v_a_3004_){
_start:
{
lean_object* v_date_3005_; lean_object* v_time_3006_; lean_object* v___x_3007_; lean_object* v_a_3008_; lean_object* v_a_3009_; lean_object* v___x_3010_; lean_object* v_a_3011_; lean_object* v_a_3012_; lean_object* v___x_3014_; uint8_t v_isShared_3015_; uint8_t v_isSharedCheck_3033_; 
v_date_3005_ = lean_ctor_get(v_d_3002_, 0);
lean_inc_ref(v_date_3005_);
v_time_3006_ = lean_ctor_get(v_d_3002_, 1);
lean_inc_ref(v_time_3006_);
lean_dec_ref(v_d_3002_);
lean_inc_ref(v_a_3003_);
v___x_3007_ = l___private_Std_Time_Notation_0__Std_Time_convertPlainDate(v_date_3005_, v_a_3003_, v_a_3004_);
lean_dec_ref(v_date_3005_);
v_a_3008_ = lean_ctor_get(v___x_3007_, 0);
lean_inc(v_a_3008_);
v_a_3009_ = lean_ctor_get(v___x_3007_, 1);
lean_inc(v_a_3009_);
lean_dec_ref(v___x_3007_);
lean_inc_ref(v_a_3003_);
v___x_3010_ = l___private_Std_Time_Notation_0__Std_Time_convertPlainTime(v_time_3006_, v_a_3003_, v_a_3009_);
v_a_3011_ = lean_ctor_get(v___x_3010_, 0);
v_a_3012_ = lean_ctor_get(v___x_3010_, 1);
v_isSharedCheck_3033_ = !lean_is_exclusive(v___x_3010_);
if (v_isSharedCheck_3033_ == 0)
{
v___x_3014_ = v___x_3010_;
v_isShared_3015_ = v_isSharedCheck_3033_;
goto v_resetjp_3013_;
}
else
{
lean_inc(v_a_3012_);
lean_inc(v_a_3011_);
lean_dec(v___x_3010_);
v___x_3014_ = lean_box(0);
v_isShared_3015_ = v_isSharedCheck_3033_;
goto v_resetjp_3013_;
}
v_resetjp_3013_:
{
lean_object* v_quotContext_3016_; lean_object* v_currMacroScope_3017_; lean_object* v_ref_3018_; uint8_t v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3031_; 
v_quotContext_3016_ = lean_ctor_get(v_a_3003_, 1);
lean_inc(v_quotContext_3016_);
v_currMacroScope_3017_ = lean_ctor_get(v_a_3003_, 2);
lean_inc(v_currMacroScope_3017_);
v_ref_3018_ = lean_ctor_get(v_a_3003_, 5);
lean_inc(v_ref_3018_);
lean_dec_ref(v_a_3003_);
v___x_3019_ = 0;
v___x_3020_ = l_Lean_SourceInfo_fromRef(v_ref_3018_, v___x_3019_);
lean_dec(v_ref_3018_);
v___x_3021_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_3022_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime___closed__1, &l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime___closed__1_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime___closed__1);
v___x_3023_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime___closed__3));
v___x_3024_ = l_Lean_addMacroScope(v_quotContext_3016_, v___x_3023_, v_currMacroScope_3017_);
v___x_3025_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime___closed__7));
lean_inc(v___x_3020_);
v___x_3026_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3026_, 0, v___x_3020_);
lean_ctor_set(v___x_3026_, 1, v___x_3022_);
lean_ctor_set(v___x_3026_, 2, v___x_3024_);
lean_ctor_set(v___x_3026_, 3, v___x_3025_);
v___x_3027_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
lean_inc(v___x_3020_);
v___x_3028_ = l_Lean_Syntax_node2(v___x_3020_, v___x_3027_, v_a_3008_, v_a_3011_);
v___x_3029_ = l_Lean_Syntax_node2(v___x_3020_, v___x_3021_, v___x_3026_, v___x_3028_);
if (v_isShared_3015_ == 0)
{
lean_ctor_set(v___x_3014_, 0, v___x_3029_);
v___x_3031_ = v___x_3014_;
goto v_reusejp_3030_;
}
else
{
lean_object* v_reuseFailAlloc_3032_; 
v_reuseFailAlloc_3032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3032_, 0, v___x_3029_);
lean_ctor_set(v_reuseFailAlloc_3032_, 1, v_a_3012_);
v___x_3031_ = v_reuseFailAlloc_3032_;
goto v_reusejp_3030_;
}
v_reusejp_3030_:
{
return v___x_3031_;
}
}
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__1(void){
_start:
{
lean_object* v___x_3035_; lean_object* v___x_3036_; 
v___x_3035_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__0));
v___x_3036_ = l_String_toRawSubstring_x27(v___x_3035_);
return v___x_3036_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__8(void){
_start:
{
lean_object* v___x_3051_; lean_object* v___x_3052_; 
v___x_3051_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__7));
v___x_3052_ = l_String_toRawSubstring_x27(v___x_3051_);
return v___x_3052_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__21(void){
_start:
{
lean_object* v___x_3079_; lean_object* v___x_3080_; 
v___x_3079_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__20));
v___x_3080_ = l_String_toRawSubstring_x27(v___x_3079_);
return v___x_3080_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime(lean_object* v_d_3087_, uint8_t v_identifier_3088_, lean_object* v_a_3089_, lean_object* v_a_3090_){
_start:
{
lean_object* v_date_3091_; lean_object* v_timezone_3092_; lean_object* v___x_3094_; uint8_t v_isShared_3095_; uint8_t v_isSharedCheck_3186_; 
v_date_3091_ = lean_ctor_get(v_d_3087_, 0);
v_timezone_3092_ = lean_ctor_get(v_d_3087_, 3);
v_isSharedCheck_3186_ = !lean_is_exclusive(v_d_3087_);
if (v_isSharedCheck_3186_ == 0)
{
lean_object* v_unused_3187_; lean_object* v_unused_3188_; 
v_unused_3187_ = lean_ctor_get(v_d_3087_, 2);
lean_dec(v_unused_3187_);
v_unused_3188_ = lean_ctor_get(v_d_3087_, 1);
lean_dec(v_unused_3188_);
v___x_3094_ = v_d_3087_;
v_isShared_3095_ = v_isSharedCheck_3186_;
goto v_resetjp_3093_;
}
else
{
lean_inc(v_timezone_3092_);
lean_inc(v_date_3091_);
lean_dec(v_d_3087_);
v___x_3094_ = lean_box(0);
v_isShared_3095_ = v_isSharedCheck_3186_;
goto v_resetjp_3093_;
}
v_resetjp_3093_:
{
lean_object* v___x_3096_; lean_object* v___x_3097_; 
v___x_3096_ = lean_thunk_get_own(v_date_3091_);
lean_dec_ref(v_date_3091_);
lean_inc_ref(v_a_3089_);
v___x_3097_ = l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime(v___x_3096_, v_a_3089_, v_a_3090_);
if (v_identifier_3088_ == 0)
{
lean_object* v_a_3098_; lean_object* v_a_3099_; lean_object* v___x_3100_; lean_object* v_a_3101_; lean_object* v_a_3102_; lean_object* v___x_3104_; uint8_t v_isShared_3105_; uint8_t v_isSharedCheck_3146_; 
v_a_3098_ = lean_ctor_get(v___x_3097_, 0);
lean_inc(v_a_3098_);
v_a_3099_ = lean_ctor_get(v___x_3097_, 1);
lean_inc(v_a_3099_);
lean_dec_ref(v___x_3097_);
lean_inc_ref(v_a_3089_);
v___x_3100_ = l___private_Std_Time_Notation_0__Std_Time_convertTimezone(v_timezone_3092_, v_a_3089_, v_a_3099_);
v_a_3101_ = lean_ctor_get(v___x_3100_, 0);
v_a_3102_ = lean_ctor_get(v___x_3100_, 1);
v_isSharedCheck_3146_ = !lean_is_exclusive(v___x_3100_);
if (v_isSharedCheck_3146_ == 0)
{
v___x_3104_ = v___x_3100_;
v_isShared_3105_ = v_isSharedCheck_3146_;
goto v_resetjp_3103_;
}
else
{
lean_inc(v_a_3102_);
lean_inc(v_a_3101_);
lean_dec(v___x_3100_);
v___x_3104_ = lean_box(0);
v_isShared_3105_ = v_isSharedCheck_3146_;
goto v_resetjp_3103_;
}
v_resetjp_3103_:
{
lean_object* v_quotContext_3106_; lean_object* v_currMacroScope_3107_; lean_object* v_ref_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3116_; 
v_quotContext_3106_ = lean_ctor_get(v_a_3089_, 1);
lean_inc(v_quotContext_3106_);
v_currMacroScope_3107_ = lean_ctor_get(v_a_3089_, 2);
lean_inc(v_currMacroScope_3107_);
v_ref_3108_ = lean_ctor_get(v_a_3089_, 5);
lean_inc(v_ref_3108_);
lean_dec_ref(v_a_3089_);
v___x_3109_ = l_Lean_SourceInfo_fromRef(v_ref_3108_, v_identifier_3088_);
lean_dec(v_ref_3108_);
v___x_3110_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_3111_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__1, &l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__1_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__1);
v___x_3112_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__4));
lean_inc(v_currMacroScope_3107_);
lean_inc(v_quotContext_3106_);
v___x_3113_ = l_Lean_addMacroScope(v_quotContext_3106_, v___x_3112_, v_currMacroScope_3107_);
v___x_3114_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__6));
lean_inc(v___x_3109_);
if (v_isShared_3095_ == 0)
{
lean_ctor_set_tag(v___x_3094_, 3);
lean_ctor_set(v___x_3094_, 3, v___x_3114_);
lean_ctor_set(v___x_3094_, 2, v___x_3113_);
lean_ctor_set(v___x_3094_, 1, v___x_3111_);
lean_ctor_set(v___x_3094_, 0, v___x_3109_);
v___x_3116_ = v___x_3094_;
goto v_reusejp_3115_;
}
else
{
lean_object* v_reuseFailAlloc_3145_; 
v_reuseFailAlloc_3145_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3145_, 0, v___x_3109_);
lean_ctor_set(v_reuseFailAlloc_3145_, 1, v___x_3111_);
lean_ctor_set(v_reuseFailAlloc_3145_, 2, v___x_3113_);
lean_ctor_set(v_reuseFailAlloc_3145_, 3, v___x_3114_);
v___x_3116_ = v_reuseFailAlloc_3145_;
goto v_reusejp_3115_;
}
v_reusejp_3115_:
{
lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3143_; 
v___x_3117_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_3118_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__42));
v___x_3119_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__44));
v___x_3120_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__45));
lean_inc(v___x_3109_);
v___x_3121_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3121_, 0, v___x_3109_);
lean_ctor_set(v___x_3121_, 1, v___x_3120_);
v___x_3122_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__47));
v___x_3123_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49);
v___x_3124_ = lean_box(0);
lean_inc(v_currMacroScope_3107_);
lean_inc(v_quotContext_3106_);
v___x_3125_ = l_Lean_addMacroScope(v_quotContext_3106_, v___x_3124_, v_currMacroScope_3107_);
v___x_3126_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__65));
lean_inc(v___x_3109_);
v___x_3127_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3127_, 0, v___x_3109_);
lean_ctor_set(v___x_3127_, 1, v___x_3123_);
lean_ctor_set(v___x_3127_, 2, v___x_3125_);
lean_ctor_set(v___x_3127_, 3, v___x_3126_);
lean_inc(v___x_3109_);
v___x_3128_ = l_Lean_Syntax_node1(v___x_3109_, v___x_3122_, v___x_3127_);
lean_inc(v___x_3109_);
v___x_3129_ = l_Lean_Syntax_node2(v___x_3109_, v___x_3119_, v___x_3121_, v___x_3128_);
v___x_3130_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__8, &l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__8_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__8);
v___x_3131_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__11));
v___x_3132_ = l_Lean_addMacroScope(v_quotContext_3106_, v___x_3131_, v_currMacroScope_3107_);
v___x_3133_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__13));
lean_inc(v___x_3109_);
v___x_3134_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3134_, 0, v___x_3109_);
lean_ctor_set(v___x_3134_, 1, v___x_3130_);
lean_ctor_set(v___x_3134_, 2, v___x_3132_);
lean_ctor_set(v___x_3134_, 3, v___x_3133_);
lean_inc(v___x_3109_);
v___x_3135_ = l_Lean_Syntax_node1(v___x_3109_, v___x_3117_, v_a_3101_);
lean_inc(v___x_3109_);
v___x_3136_ = l_Lean_Syntax_node2(v___x_3109_, v___x_3110_, v___x_3134_, v___x_3135_);
v___x_3137_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__72));
lean_inc(v___x_3109_);
v___x_3138_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3138_, 0, v___x_3109_);
lean_ctor_set(v___x_3138_, 1, v___x_3137_);
lean_inc(v___x_3109_);
v___x_3139_ = l_Lean_Syntax_node3(v___x_3109_, v___x_3118_, v___x_3129_, v___x_3136_, v___x_3138_);
lean_inc(v___x_3109_);
v___x_3140_ = l_Lean_Syntax_node2(v___x_3109_, v___x_3117_, v_a_3098_, v___x_3139_);
v___x_3141_ = l_Lean_Syntax_node2(v___x_3109_, v___x_3110_, v___x_3116_, v___x_3140_);
if (v_isShared_3105_ == 0)
{
lean_ctor_set(v___x_3104_, 0, v___x_3141_);
v___x_3143_ = v___x_3104_;
goto v_reusejp_3142_;
}
else
{
lean_object* v_reuseFailAlloc_3144_; 
v_reuseFailAlloc_3144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3144_, 0, v___x_3141_);
lean_ctor_set(v_reuseFailAlloc_3144_, 1, v_a_3102_);
v___x_3143_ = v_reuseFailAlloc_3144_;
goto v_reusejp_3142_;
}
v_reusejp_3142_:
{
return v___x_3143_;
}
}
}
}
else
{
lean_object* v_a_3147_; lean_object* v_a_3148_; lean_object* v___x_3150_; uint8_t v_isShared_3151_; uint8_t v_isSharedCheck_3185_; 
v_a_3147_ = lean_ctor_get(v___x_3097_, 0);
v_a_3148_ = lean_ctor_get(v___x_3097_, 1);
v_isSharedCheck_3185_ = !lean_is_exclusive(v___x_3097_);
if (v_isSharedCheck_3185_ == 0)
{
v___x_3150_ = v___x_3097_;
v_isShared_3151_ = v_isSharedCheck_3185_;
goto v_resetjp_3149_;
}
else
{
lean_inc(v_a_3148_);
lean_inc(v_a_3147_);
lean_dec(v___x_3097_);
v___x_3150_ = lean_box(0);
v_isShared_3151_ = v_isSharedCheck_3185_;
goto v_resetjp_3149_;
}
v_resetjp_3149_:
{
lean_object* v_quotContext_3152_; lean_object* v_currMacroScope_3153_; lean_object* v_ref_3154_; uint8_t v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3163_; 
v_quotContext_3152_ = lean_ctor_get(v_a_3089_, 1);
lean_inc(v_quotContext_3152_);
v_currMacroScope_3153_ = lean_ctor_get(v_a_3089_, 2);
lean_inc(v_currMacroScope_3153_);
v_ref_3154_ = lean_ctor_get(v_a_3089_, 5);
lean_inc(v_ref_3154_);
lean_dec_ref(v_a_3089_);
v___x_3155_ = 0;
v___x_3156_ = l_Lean_SourceInfo_fromRef(v_ref_3154_, v___x_3155_);
lean_dec(v_ref_3154_);
v___x_3157_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_3158_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__1, &l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__1_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__1);
v___x_3159_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__4));
lean_inc(v_currMacroScope_3153_);
lean_inc(v_quotContext_3152_);
v___x_3160_ = l_Lean_addMacroScope(v_quotContext_3152_, v___x_3159_, v_currMacroScope_3153_);
v___x_3161_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__6));
lean_inc(v___x_3156_);
if (v_isShared_3095_ == 0)
{
lean_ctor_set_tag(v___x_3094_, 3);
lean_ctor_set(v___x_3094_, 3, v___x_3161_);
lean_ctor_set(v___x_3094_, 2, v___x_3160_);
lean_ctor_set(v___x_3094_, 1, v___x_3158_);
lean_ctor_set(v___x_3094_, 0, v___x_3156_);
v___x_3163_ = v___x_3094_;
goto v_reusejp_3162_;
}
else
{
lean_object* v_reuseFailAlloc_3184_; 
v_reuseFailAlloc_3184_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3184_, 0, v___x_3156_);
lean_ctor_set(v_reuseFailAlloc_3184_, 1, v___x_3158_);
lean_ctor_set(v_reuseFailAlloc_3184_, 2, v___x_3160_);
lean_ctor_set(v_reuseFailAlloc_3184_, 3, v___x_3161_);
v___x_3163_ = v_reuseFailAlloc_3184_;
goto v_reusejp_3162_;
}
v_reusejp_3162_:
{
lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v_name_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3182_; 
v___x_3164_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
lean_inc(v___x_3156_);
v___x_3165_ = l_Lean_Syntax_node1(v___x_3156_, v___x_3164_, v_a_3147_);
lean_inc(v___x_3156_);
v___x_3166_ = l_Lean_Syntax_node2(v___x_3156_, v___x_3157_, v___x_3163_, v___x_3165_);
v_name_3167_ = lean_ctor_get(v_timezone_3092_, 1);
lean_inc_ref(v_name_3167_);
lean_dec_ref(v_timezone_3092_);
v___x_3168_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__14));
lean_inc(v___x_3156_);
v___x_3169_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3169_, 0, v___x_3156_);
lean_ctor_set(v___x_3169_, 1, v___x_3168_);
v___x_3170_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__17));
v___x_3171_ = l_Lean_addMacroScope(v_quotContext_3152_, v___x_3170_, v_currMacroScope_3153_);
v___x_3172_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__19));
v___x_3173_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__21, &l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__21_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__21);
v___x_3174_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__23));
lean_inc(v___x_3156_);
v___x_3175_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3175_, 0, v___x_3156_);
lean_ctor_set(v___x_3175_, 1, v___x_3173_);
lean_ctor_set(v___x_3175_, 2, v___x_3171_);
lean_ctor_set(v___x_3175_, 3, v___x_3174_);
v___x_3176_ = lean_box(2);
v___x_3177_ = l_Lean_Syntax_mkStrLit(v_name_3167_, v___x_3176_);
lean_inc(v___x_3156_);
v___x_3178_ = l_Lean_Syntax_node1(v___x_3156_, v___x_3164_, v___x_3177_);
lean_inc(v___x_3156_);
v___x_3179_ = l_Lean_Syntax_node2(v___x_3156_, v___x_3157_, v___x_3175_, v___x_3178_);
v___x_3180_ = l_Lean_Syntax_node3(v___x_3156_, v___x_3172_, v___x_3166_, v___x_3169_, v___x_3179_);
if (v_isShared_3151_ == 0)
{
lean_ctor_set(v___x_3150_, 0, v___x_3180_);
v___x_3182_ = v___x_3150_;
goto v_reusejp_3181_;
}
else
{
lean_object* v_reuseFailAlloc_3183_; 
v_reuseFailAlloc_3183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3183_, 0, v___x_3180_);
lean_ctor_set(v_reuseFailAlloc_3183_, 1, v_a_3148_);
v___x_3182_ = v_reuseFailAlloc_3183_;
goto v_reusejp_3181_;
}
v_reusejp_3181_:
{
return v___x_3182_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___boxed(lean_object* v_d_3189_, lean_object* v_identifier_3190_, lean_object* v_a_3191_, lean_object* v_a_3192_){
_start:
{
uint8_t v_identifier_boxed_3193_; lean_object* v_res_3194_; 
v_identifier_boxed_3193_ = lean_unbox(v_identifier_3190_);
v_res_3194_ = l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime(v_d_3189_, v_identifier_boxed_3193_, v_a_3191_, v_a_3192_);
return v_res_3194_;
}
}
LEAN_EXPORT lean_object* l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termZoned_x28___x29__1(lean_object* v_x_3360_, lean_object* v_a_3361_, lean_object* v_a_3362_){
_start:
{
lean_object* v___x_3363_; uint8_t v___x_3364_; 
v___x_3363_ = ((lean_object*)(l_Std_Time_termZoned_x28___x29___closed__1));
lean_inc(v_x_3360_);
v___x_3364_ = l_Lean_Syntax_isOfKind(v_x_3360_, v___x_3363_);
if (v___x_3364_ == 0)
{
lean_object* v___x_3365_; lean_object* v___x_3366_; 
lean_dec(v_x_3360_);
v___x_3365_ = lean_box(1);
v___x_3366_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3366_, 0, v___x_3365_);
lean_ctor_set(v___x_3366_, 1, v_a_3362_);
return v___x_3366_;
}
else
{
lean_object* v___x_3367_; lean_object* v_date_3368_; lean_object* v___x_3369_; uint8_t v___x_3370_; 
v___x_3367_ = lean_unsigned_to_nat(1u);
v_date_3368_ = l_Lean_Syntax_getArg(v_x_3360_, v___x_3367_);
lean_dec(v_x_3360_);
v___x_3369_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxString___closed__1));
lean_inc(v_date_3368_);
v___x_3370_ = l_Lean_Syntax_isOfKind(v_date_3368_, v___x_3369_);
if (v___x_3370_ == 0)
{
lean_object* v___x_3371_; lean_object* v___x_3372_; 
lean_dec(v_date_3368_);
v___x_3371_ = lean_box(1);
v___x_3372_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3372_, 0, v___x_3371_);
lean_ctor_set(v___x_3372_, 1, v_a_3362_);
return v___x_3372_;
}
else
{
lean_object* v___x_3373_; lean_object* v___x_3374_; 
v___x_3373_ = l_Lean_TSyntax_getString(v_date_3368_);
lean_inc_ref(v___x_3373_);
v___x_3374_ = l_Std_Time_ZonedDateTime_fromLeanDateTimeWithZoneString(v___x_3373_);
if (lean_obj_tag(v___x_3374_) == 0)
{
lean_object* v___x_3375_; 
lean_dec_ref(v___x_3374_);
v___x_3375_ = l_Std_Time_ZonedDateTime_fromLeanDateTimeWithIdentifierString(v___x_3373_);
if (lean_obj_tag(v___x_3375_) == 0)
{
lean_object* v_a_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; 
v_a_3376_ = lean_ctor_get(v___x_3375_, 0);
lean_inc(v_a_3376_);
lean_dec_ref(v___x_3375_);
v___x_3377_ = ((lean_object*)(l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termZoned_x28___x29__1___closed__0));
v___x_3378_ = lean_string_append(v___x_3377_, v_a_3376_);
lean_dec(v_a_3376_);
v___x_3379_ = l_Lean_Macro_throwErrorAt___redArg(v_date_3368_, v___x_3378_, v_a_3361_, v_a_3362_);
lean_dec(v_date_3368_);
return v___x_3379_;
}
else
{
lean_object* v_a_3380_; lean_object* v___x_3381_; lean_object* v_a_3382_; lean_object* v_a_3383_; lean_object* v___x_3385_; uint8_t v_isShared_3386_; uint8_t v_isSharedCheck_3390_; 
lean_dec(v_date_3368_);
v_a_3380_ = lean_ctor_get(v___x_3375_, 0);
lean_inc(v_a_3380_);
lean_dec_ref(v___x_3375_);
lean_inc_ref(v_a_3361_);
v___x_3381_ = l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime(v_a_3380_, v___x_3370_, v_a_3361_, v_a_3362_);
v_a_3382_ = lean_ctor_get(v___x_3381_, 0);
v_a_3383_ = lean_ctor_get(v___x_3381_, 1);
v_isSharedCheck_3390_ = !lean_is_exclusive(v___x_3381_);
if (v_isSharedCheck_3390_ == 0)
{
v___x_3385_ = v___x_3381_;
v_isShared_3386_ = v_isSharedCheck_3390_;
goto v_resetjp_3384_;
}
else
{
lean_inc(v_a_3383_);
lean_inc(v_a_3382_);
lean_dec(v___x_3381_);
v___x_3385_ = lean_box(0);
v_isShared_3386_ = v_isSharedCheck_3390_;
goto v_resetjp_3384_;
}
v_resetjp_3384_:
{
lean_object* v___x_3388_; 
if (v_isShared_3386_ == 0)
{
v___x_3388_ = v___x_3385_;
goto v_reusejp_3387_;
}
else
{
lean_object* v_reuseFailAlloc_3389_; 
v_reuseFailAlloc_3389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3389_, 0, v_a_3382_);
lean_ctor_set(v_reuseFailAlloc_3389_, 1, v_a_3383_);
v___x_3388_ = v_reuseFailAlloc_3389_;
goto v_reusejp_3387_;
}
v_reusejp_3387_:
{
return v___x_3388_;
}
}
}
}
else
{
lean_object* v_a_3391_; uint8_t v___x_3392_; lean_object* v___x_3393_; lean_object* v_a_3394_; lean_object* v_a_3395_; lean_object* v___x_3397_; uint8_t v_isShared_3398_; uint8_t v_isSharedCheck_3402_; 
lean_dec_ref(v___x_3373_);
lean_dec(v_date_3368_);
v_a_3391_ = lean_ctor_get(v___x_3374_, 0);
lean_inc(v_a_3391_);
lean_dec_ref(v___x_3374_);
v___x_3392_ = 0;
lean_inc_ref(v_a_3361_);
v___x_3393_ = l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime(v_a_3391_, v___x_3392_, v_a_3361_, v_a_3362_);
v_a_3394_ = lean_ctor_get(v___x_3393_, 0);
v_a_3395_ = lean_ctor_get(v___x_3393_, 1);
v_isSharedCheck_3402_ = !lean_is_exclusive(v___x_3393_);
if (v_isSharedCheck_3402_ == 0)
{
v___x_3397_ = v___x_3393_;
v_isShared_3398_ = v_isSharedCheck_3402_;
goto v_resetjp_3396_;
}
else
{
lean_inc(v_a_3395_);
lean_inc(v_a_3394_);
lean_dec(v___x_3393_);
v___x_3397_ = lean_box(0);
v_isShared_3398_ = v_isSharedCheck_3402_;
goto v_resetjp_3396_;
}
v_resetjp_3396_:
{
lean_object* v___x_3400_; 
if (v_isShared_3398_ == 0)
{
v___x_3400_ = v___x_3397_;
goto v_reusejp_3399_;
}
else
{
lean_object* v_reuseFailAlloc_3401_; 
v_reuseFailAlloc_3401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3401_, 0, v_a_3394_);
lean_ctor_set(v_reuseFailAlloc_3401_, 1, v_a_3395_);
v___x_3400_ = v_reuseFailAlloc_3401_;
goto v_reusejp_3399_;
}
v_reusejp_3399_:
{
return v___x_3400_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termZoned_x28___x29__1___boxed(lean_object* v_x_3403_, lean_object* v_a_3404_, lean_object* v_a_3405_){
_start:
{
lean_object* v_res_3406_; 
v_res_3406_ = l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termZoned_x28___x29__1(v_x_3403_, v_a_3404_, v_a_3405_);
lean_dec_ref(v_a_3404_);
return v_res_3406_;
}
}
LEAN_EXPORT lean_object* l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termZoned_x28___x2c___x29__1(lean_object* v_x_3407_, lean_object* v_a_3408_, lean_object* v_a_3409_){
_start:
{
lean_object* v___x_3410_; uint8_t v___x_3411_; 
v___x_3410_ = ((lean_object*)(l_Std_Time_termZoned_x28___x2c___x29___closed__1));
lean_inc(v_x_3407_);
v___x_3411_ = l_Lean_Syntax_isOfKind(v_x_3407_, v___x_3410_);
if (v___x_3411_ == 0)
{
lean_object* v___x_3412_; lean_object* v___x_3413_; 
lean_dec_ref(v_a_3408_);
lean_dec(v_x_3407_);
v___x_3412_ = lean_box(1);
v___x_3413_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3413_, 0, v___x_3412_);
lean_ctor_set(v___x_3413_, 1, v_a_3409_);
return v___x_3413_;
}
else
{
lean_object* v___x_3414_; lean_object* v_date_3415_; lean_object* v___x_3416_; uint8_t v___x_3417_; 
v___x_3414_ = lean_unsigned_to_nat(1u);
v_date_3415_ = l_Lean_Syntax_getArg(v_x_3407_, v___x_3414_);
v___x_3416_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxString___closed__1));
lean_inc(v_date_3415_);
v___x_3417_ = l_Lean_Syntax_isOfKind(v_date_3415_, v___x_3416_);
if (v___x_3417_ == 0)
{
lean_object* v___x_3418_; lean_object* v___x_3419_; 
lean_dec(v_date_3415_);
lean_dec_ref(v_a_3408_);
lean_dec(v_x_3407_);
v___x_3418_ = lean_box(1);
v___x_3419_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3419_, 0, v___x_3418_);
lean_ctor_set(v___x_3419_, 1, v_a_3409_);
return v___x_3419_;
}
else
{
lean_object* v___x_3420_; lean_object* v___x_3421_; 
v___x_3420_ = l_Lean_TSyntax_getString(v_date_3415_);
v___x_3421_ = l_Std_Time_PlainDateTime_fromLeanDateTimeString(v___x_3420_);
if (lean_obj_tag(v___x_3421_) == 0)
{
lean_object* v_a_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; 
lean_dec(v_x_3407_);
v_a_3422_ = lean_ctor_get(v___x_3421_, 0);
lean_inc(v_a_3422_);
lean_dec_ref(v___x_3421_);
v___x_3423_ = ((lean_object*)(l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termZoned_x28___x29__1___closed__0));
v___x_3424_ = lean_string_append(v___x_3423_, v_a_3422_);
lean_dec(v_a_3422_);
v___x_3425_ = l_Lean_Macro_throwErrorAt___redArg(v_date_3415_, v___x_3424_, v_a_3408_, v_a_3409_);
lean_dec_ref(v_a_3408_);
lean_dec(v_date_3415_);
return v___x_3425_;
}
else
{
lean_object* v_a_3426_; lean_object* v___x_3427_; lean_object* v_a_3428_; lean_object* v_a_3429_; lean_object* v___x_3431_; uint8_t v_isShared_3432_; uint8_t v_isSharedCheck_3452_; 
lean_dec(v_date_3415_);
v_a_3426_ = lean_ctor_get(v___x_3421_, 0);
lean_inc(v_a_3426_);
lean_dec_ref(v___x_3421_);
lean_inc_ref(v_a_3408_);
v___x_3427_ = l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime(v_a_3426_, v_a_3408_, v_a_3409_);
v_a_3428_ = lean_ctor_get(v___x_3427_, 0);
v_a_3429_ = lean_ctor_get(v___x_3427_, 1);
v_isSharedCheck_3452_ = !lean_is_exclusive(v___x_3427_);
if (v_isSharedCheck_3452_ == 0)
{
v___x_3431_ = v___x_3427_;
v_isShared_3432_ = v_isSharedCheck_3452_;
goto v_resetjp_3430_;
}
else
{
lean_inc(v_a_3429_);
lean_inc(v_a_3428_);
lean_dec(v___x_3427_);
v___x_3431_ = lean_box(0);
v_isShared_3432_ = v_isSharedCheck_3452_;
goto v_resetjp_3430_;
}
v_resetjp_3430_:
{
lean_object* v_quotContext_3433_; lean_object* v_currMacroScope_3434_; lean_object* v_ref_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; uint8_t v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3450_; 
v_quotContext_3433_ = lean_ctor_get(v_a_3408_, 1);
lean_inc(v_quotContext_3433_);
v_currMacroScope_3434_ = lean_ctor_get(v_a_3408_, 2);
lean_inc(v_currMacroScope_3434_);
v_ref_3435_ = lean_ctor_get(v_a_3408_, 5);
lean_inc(v_ref_3435_);
lean_dec_ref(v_a_3408_);
v___x_3436_ = lean_unsigned_to_nat(3u);
v___x_3437_ = l_Lean_Syntax_getArg(v_x_3407_, v___x_3436_);
lean_dec(v_x_3407_);
v___x_3438_ = 0;
v___x_3439_ = l_Lean_SourceInfo_fromRef(v_ref_3435_, v___x_3438_);
lean_dec(v_ref_3435_);
v___x_3440_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_3441_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__1, &l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__1_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__1);
v___x_3442_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__4));
v___x_3443_ = l_Lean_addMacroScope(v_quotContext_3433_, v___x_3442_, v_currMacroScope_3434_);
v___x_3444_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__6));
lean_inc(v___x_3439_);
v___x_3445_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3445_, 0, v___x_3439_);
lean_ctor_set(v___x_3445_, 1, v___x_3441_);
lean_ctor_set(v___x_3445_, 2, v___x_3443_);
lean_ctor_set(v___x_3445_, 3, v___x_3444_);
v___x_3446_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
lean_inc(v___x_3439_);
v___x_3447_ = l_Lean_Syntax_node2(v___x_3439_, v___x_3446_, v_a_3428_, v___x_3437_);
v___x_3448_ = l_Lean_Syntax_node2(v___x_3439_, v___x_3440_, v___x_3445_, v___x_3447_);
if (v_isShared_3432_ == 0)
{
lean_ctor_set(v___x_3431_, 0, v___x_3448_);
v___x_3450_ = v___x_3431_;
goto v_reusejp_3449_;
}
else
{
lean_object* v_reuseFailAlloc_3451_; 
v_reuseFailAlloc_3451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3451_, 0, v___x_3448_);
lean_ctor_set(v_reuseFailAlloc_3451_, 1, v_a_3429_);
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
}
}
}
LEAN_EXPORT lean_object* l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termDatetime_x28___x29__1(lean_object* v_x_3453_, lean_object* v_a_3454_, lean_object* v_a_3455_){
_start:
{
lean_object* v___x_3456_; uint8_t v___x_3457_; 
v___x_3456_ = ((lean_object*)(l_Std_Time_termDatetime_x28___x29___closed__1));
lean_inc(v_x_3453_);
v___x_3457_ = l_Lean_Syntax_isOfKind(v_x_3453_, v___x_3456_);
if (v___x_3457_ == 0)
{
lean_object* v___x_3458_; lean_object* v___x_3459_; 
lean_dec(v_x_3453_);
v___x_3458_ = lean_box(1);
v___x_3459_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3459_, 0, v___x_3458_);
lean_ctor_set(v___x_3459_, 1, v_a_3455_);
return v___x_3459_;
}
else
{
lean_object* v___x_3460_; lean_object* v_date_3461_; lean_object* v___x_3462_; uint8_t v___x_3463_; 
v___x_3460_ = lean_unsigned_to_nat(1u);
v_date_3461_ = l_Lean_Syntax_getArg(v_x_3453_, v___x_3460_);
lean_dec(v_x_3453_);
v___x_3462_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxString___closed__1));
lean_inc(v_date_3461_);
v___x_3463_ = l_Lean_Syntax_isOfKind(v_date_3461_, v___x_3462_);
if (v___x_3463_ == 0)
{
lean_object* v___x_3464_; lean_object* v___x_3465_; 
lean_dec(v_date_3461_);
v___x_3464_ = lean_box(1);
v___x_3465_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3465_, 0, v___x_3464_);
lean_ctor_set(v___x_3465_, 1, v_a_3455_);
return v___x_3465_;
}
else
{
lean_object* v___x_3466_; lean_object* v___x_3467_; 
v___x_3466_ = l_Lean_TSyntax_getString(v_date_3461_);
v___x_3467_ = l_Std_Time_PlainDateTime_fromLeanDateTimeString(v___x_3466_);
if (lean_obj_tag(v___x_3467_) == 0)
{
lean_object* v_a_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; 
v_a_3468_ = lean_ctor_get(v___x_3467_, 0);
lean_inc(v_a_3468_);
lean_dec_ref(v___x_3467_);
v___x_3469_ = ((lean_object*)(l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termZoned_x28___x29__1___closed__0));
v___x_3470_ = lean_string_append(v___x_3469_, v_a_3468_);
lean_dec(v_a_3468_);
v___x_3471_ = l_Lean_Macro_throwErrorAt___redArg(v_date_3461_, v___x_3470_, v_a_3454_, v_a_3455_);
lean_dec(v_date_3461_);
return v___x_3471_;
}
else
{
lean_object* v_a_3472_; lean_object* v___x_3473_; lean_object* v_a_3474_; lean_object* v_a_3475_; lean_object* v___x_3477_; uint8_t v_isShared_3478_; uint8_t v_isSharedCheck_3482_; 
lean_dec(v_date_3461_);
v_a_3472_ = lean_ctor_get(v___x_3467_, 0);
lean_inc(v_a_3472_);
lean_dec_ref(v___x_3467_);
lean_inc_ref(v_a_3454_);
v___x_3473_ = l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime(v_a_3472_, v_a_3454_, v_a_3455_);
v_a_3474_ = lean_ctor_get(v___x_3473_, 0);
v_a_3475_ = lean_ctor_get(v___x_3473_, 1);
v_isSharedCheck_3482_ = !lean_is_exclusive(v___x_3473_);
if (v_isSharedCheck_3482_ == 0)
{
v___x_3477_ = v___x_3473_;
v_isShared_3478_ = v_isSharedCheck_3482_;
goto v_resetjp_3476_;
}
else
{
lean_inc(v_a_3475_);
lean_inc(v_a_3474_);
lean_dec(v___x_3473_);
v___x_3477_ = lean_box(0);
v_isShared_3478_ = v_isSharedCheck_3482_;
goto v_resetjp_3476_;
}
v_resetjp_3476_:
{
lean_object* v___x_3480_; 
if (v_isShared_3478_ == 0)
{
v___x_3480_ = v___x_3477_;
goto v_reusejp_3479_;
}
else
{
lean_object* v_reuseFailAlloc_3481_; 
v_reuseFailAlloc_3481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3481_, 0, v_a_3474_);
lean_ctor_set(v_reuseFailAlloc_3481_, 1, v_a_3475_);
v___x_3480_ = v_reuseFailAlloc_3481_;
goto v_reusejp_3479_;
}
v_reusejp_3479_:
{
return v___x_3480_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termDatetime_x28___x29__1___boxed(lean_object* v_x_3483_, lean_object* v_a_3484_, lean_object* v_a_3485_){
_start:
{
lean_object* v_res_3486_; 
v_res_3486_ = l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termDatetime_x28___x29__1(v_x_3483_, v_a_3484_, v_a_3485_);
lean_dec_ref(v_a_3484_);
return v_res_3486_;
}
}
LEAN_EXPORT lean_object* l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termDate_x28___x29__1(lean_object* v_x_3487_, lean_object* v_a_3488_, lean_object* v_a_3489_){
_start:
{
lean_object* v___x_3490_; uint8_t v___x_3491_; 
v___x_3490_ = ((lean_object*)(l_Std_Time_termDate_x28___x29___closed__1));
lean_inc(v_x_3487_);
v___x_3491_ = l_Lean_Syntax_isOfKind(v_x_3487_, v___x_3490_);
if (v___x_3491_ == 0)
{
lean_object* v___x_3492_; lean_object* v___x_3493_; 
lean_dec(v_x_3487_);
v___x_3492_ = lean_box(1);
v___x_3493_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3493_, 0, v___x_3492_);
lean_ctor_set(v___x_3493_, 1, v_a_3489_);
return v___x_3493_;
}
else
{
lean_object* v___x_3494_; lean_object* v_date_3495_; lean_object* v___x_3496_; uint8_t v___x_3497_; 
v___x_3494_ = lean_unsigned_to_nat(1u);
v_date_3495_ = l_Lean_Syntax_getArg(v_x_3487_, v___x_3494_);
lean_dec(v_x_3487_);
v___x_3496_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxString___closed__1));
lean_inc(v_date_3495_);
v___x_3497_ = l_Lean_Syntax_isOfKind(v_date_3495_, v___x_3496_);
if (v___x_3497_ == 0)
{
lean_object* v___x_3498_; lean_object* v___x_3499_; 
lean_dec(v_date_3495_);
v___x_3498_ = lean_box(1);
v___x_3499_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3499_, 0, v___x_3498_);
lean_ctor_set(v___x_3499_, 1, v_a_3489_);
return v___x_3499_;
}
else
{
lean_object* v___x_3500_; lean_object* v___x_3501_; 
v___x_3500_ = l_Lean_TSyntax_getString(v_date_3495_);
v___x_3501_ = l_Std_Time_PlainDate_fromSQLDateString(v___x_3500_);
if (lean_obj_tag(v___x_3501_) == 0)
{
lean_object* v_a_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; 
v_a_3502_ = lean_ctor_get(v___x_3501_, 0);
lean_inc(v_a_3502_);
lean_dec_ref(v___x_3501_);
v___x_3503_ = ((lean_object*)(l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termZoned_x28___x29__1___closed__0));
v___x_3504_ = lean_string_append(v___x_3503_, v_a_3502_);
lean_dec(v_a_3502_);
v___x_3505_ = l_Lean_Macro_throwErrorAt___redArg(v_date_3495_, v___x_3504_, v_a_3488_, v_a_3489_);
lean_dec(v_date_3495_);
return v___x_3505_;
}
else
{
lean_object* v_a_3506_; lean_object* v___x_3507_; lean_object* v_a_3508_; lean_object* v_a_3509_; lean_object* v___x_3511_; uint8_t v_isShared_3512_; uint8_t v_isSharedCheck_3516_; 
lean_dec(v_date_3495_);
v_a_3506_ = lean_ctor_get(v___x_3501_, 0);
lean_inc(v_a_3506_);
lean_dec_ref(v___x_3501_);
lean_inc_ref(v_a_3488_);
v___x_3507_ = l___private_Std_Time_Notation_0__Std_Time_convertPlainDate(v_a_3506_, v_a_3488_, v_a_3489_);
lean_dec(v_a_3506_);
v_a_3508_ = lean_ctor_get(v___x_3507_, 0);
v_a_3509_ = lean_ctor_get(v___x_3507_, 1);
v_isSharedCheck_3516_ = !lean_is_exclusive(v___x_3507_);
if (v_isSharedCheck_3516_ == 0)
{
v___x_3511_ = v___x_3507_;
v_isShared_3512_ = v_isSharedCheck_3516_;
goto v_resetjp_3510_;
}
else
{
lean_inc(v_a_3509_);
lean_inc(v_a_3508_);
lean_dec(v___x_3507_);
v___x_3511_ = lean_box(0);
v_isShared_3512_ = v_isSharedCheck_3516_;
goto v_resetjp_3510_;
}
v_resetjp_3510_:
{
lean_object* v___x_3514_; 
if (v_isShared_3512_ == 0)
{
v___x_3514_ = v___x_3511_;
goto v_reusejp_3513_;
}
else
{
lean_object* v_reuseFailAlloc_3515_; 
v_reuseFailAlloc_3515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3515_, 0, v_a_3508_);
lean_ctor_set(v_reuseFailAlloc_3515_, 1, v_a_3509_);
v___x_3514_ = v_reuseFailAlloc_3515_;
goto v_reusejp_3513_;
}
v_reusejp_3513_:
{
return v___x_3514_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termDate_x28___x29__1___boxed(lean_object* v_x_3517_, lean_object* v_a_3518_, lean_object* v_a_3519_){
_start:
{
lean_object* v_res_3520_; 
v_res_3520_ = l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termDate_x28___x29__1(v_x_3517_, v_a_3518_, v_a_3519_);
lean_dec_ref(v_a_3518_);
return v_res_3520_;
}
}
LEAN_EXPORT lean_object* l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termTime_x28___x29__1(lean_object* v_x_3521_, lean_object* v_a_3522_, lean_object* v_a_3523_){
_start:
{
lean_object* v___x_3524_; uint8_t v___x_3525_; 
v___x_3524_ = ((lean_object*)(l_Std_Time_termTime_x28___x29___closed__1));
lean_inc(v_x_3521_);
v___x_3525_ = l_Lean_Syntax_isOfKind(v_x_3521_, v___x_3524_);
if (v___x_3525_ == 0)
{
lean_object* v___x_3526_; lean_object* v___x_3527_; 
lean_dec(v_x_3521_);
v___x_3526_ = lean_box(1);
v___x_3527_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3527_, 0, v___x_3526_);
lean_ctor_set(v___x_3527_, 1, v_a_3523_);
return v___x_3527_;
}
else
{
lean_object* v___x_3528_; lean_object* v_time_3529_; lean_object* v___x_3530_; uint8_t v___x_3531_; 
v___x_3528_ = lean_unsigned_to_nat(1u);
v_time_3529_ = l_Lean_Syntax_getArg(v_x_3521_, v___x_3528_);
lean_dec(v_x_3521_);
v___x_3530_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxString___closed__1));
lean_inc(v_time_3529_);
v___x_3531_ = l_Lean_Syntax_isOfKind(v_time_3529_, v___x_3530_);
if (v___x_3531_ == 0)
{
lean_object* v___x_3532_; lean_object* v___x_3533_; 
lean_dec(v_time_3529_);
v___x_3532_ = lean_box(1);
v___x_3533_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3533_, 0, v___x_3532_);
lean_ctor_set(v___x_3533_, 1, v_a_3523_);
return v___x_3533_;
}
else
{
lean_object* v___x_3534_; lean_object* v___x_3535_; 
v___x_3534_ = l_Lean_TSyntax_getString(v_time_3529_);
v___x_3535_ = l_Std_Time_PlainTime_fromLeanTime24Hour(v___x_3534_);
if (lean_obj_tag(v___x_3535_) == 0)
{
lean_object* v_a_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; 
v_a_3536_ = lean_ctor_get(v___x_3535_, 0);
lean_inc(v_a_3536_);
lean_dec_ref(v___x_3535_);
v___x_3537_ = ((lean_object*)(l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termZoned_x28___x29__1___closed__0));
v___x_3538_ = lean_string_append(v___x_3537_, v_a_3536_);
lean_dec(v_a_3536_);
v___x_3539_ = l_Lean_Macro_throwErrorAt___redArg(v_time_3529_, v___x_3538_, v_a_3522_, v_a_3523_);
lean_dec(v_time_3529_);
return v___x_3539_;
}
else
{
lean_object* v_a_3540_; lean_object* v___x_3541_; lean_object* v_a_3542_; lean_object* v_a_3543_; lean_object* v___x_3545_; uint8_t v_isShared_3546_; uint8_t v_isSharedCheck_3550_; 
lean_dec(v_time_3529_);
v_a_3540_ = lean_ctor_get(v___x_3535_, 0);
lean_inc(v_a_3540_);
lean_dec_ref(v___x_3535_);
lean_inc_ref(v_a_3522_);
v___x_3541_ = l___private_Std_Time_Notation_0__Std_Time_convertPlainTime(v_a_3540_, v_a_3522_, v_a_3523_);
v_a_3542_ = lean_ctor_get(v___x_3541_, 0);
v_a_3543_ = lean_ctor_get(v___x_3541_, 1);
v_isSharedCheck_3550_ = !lean_is_exclusive(v___x_3541_);
if (v_isSharedCheck_3550_ == 0)
{
v___x_3545_ = v___x_3541_;
v_isShared_3546_ = v_isSharedCheck_3550_;
goto v_resetjp_3544_;
}
else
{
lean_inc(v_a_3543_);
lean_inc(v_a_3542_);
lean_dec(v___x_3541_);
v___x_3545_ = lean_box(0);
v_isShared_3546_ = v_isSharedCheck_3550_;
goto v_resetjp_3544_;
}
v_resetjp_3544_:
{
lean_object* v___x_3548_; 
if (v_isShared_3546_ == 0)
{
v___x_3548_ = v___x_3545_;
goto v_reusejp_3547_;
}
else
{
lean_object* v_reuseFailAlloc_3549_; 
v_reuseFailAlloc_3549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3549_, 0, v_a_3542_);
lean_ctor_set(v_reuseFailAlloc_3549_, 1, v_a_3543_);
v___x_3548_ = v_reuseFailAlloc_3549_;
goto v_reusejp_3547_;
}
v_reusejp_3547_:
{
return v___x_3548_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termTime_x28___x29__1___boxed(lean_object* v_x_3551_, lean_object* v_a_3552_, lean_object* v_a_3553_){
_start:
{
lean_object* v_res_3554_; 
v_res_3554_ = l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termTime_x28___x29__1(v_x_3551_, v_a_3552_, v_a_3553_);
lean_dec_ref(v_a_3552_);
return v_res_3554_;
}
}
LEAN_EXPORT lean_object* l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termOffset_x28___x29__1(lean_object* v_x_3555_, lean_object* v_a_3556_, lean_object* v_a_3557_){
_start:
{
lean_object* v___x_3558_; uint8_t v___x_3559_; 
v___x_3558_ = ((lean_object*)(l_Std_Time_termOffset_x28___x29___closed__1));
lean_inc(v_x_3555_);
v___x_3559_ = l_Lean_Syntax_isOfKind(v_x_3555_, v___x_3558_);
if (v___x_3559_ == 0)
{
lean_object* v___x_3560_; lean_object* v___x_3561_; 
lean_dec(v_x_3555_);
v___x_3560_ = lean_box(1);
v___x_3561_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3561_, 0, v___x_3560_);
lean_ctor_set(v___x_3561_, 1, v_a_3557_);
return v___x_3561_;
}
else
{
lean_object* v___x_3562_; lean_object* v_offset_3563_; lean_object* v___x_3564_; uint8_t v___x_3565_; 
v___x_3562_ = lean_unsigned_to_nat(1u);
v_offset_3563_ = l_Lean_Syntax_getArg(v_x_3555_, v___x_3562_);
lean_dec(v_x_3555_);
v___x_3564_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxString___closed__1));
lean_inc(v_offset_3563_);
v___x_3565_ = l_Lean_Syntax_isOfKind(v_offset_3563_, v___x_3564_);
if (v___x_3565_ == 0)
{
lean_object* v___x_3566_; lean_object* v___x_3567_; 
lean_dec(v_offset_3563_);
v___x_3566_ = lean_box(1);
v___x_3567_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3567_, 0, v___x_3566_);
lean_ctor_set(v___x_3567_, 1, v_a_3557_);
return v___x_3567_;
}
else
{
lean_object* v___x_3568_; lean_object* v___x_3569_; 
v___x_3568_ = l_Lean_TSyntax_getString(v_offset_3563_);
v___x_3569_ = l_Std_Time_TimeZone_Offset_fromOffset(v___x_3568_);
if (lean_obj_tag(v___x_3569_) == 0)
{
lean_object* v_a_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; 
v_a_3570_ = lean_ctor_get(v___x_3569_, 0);
lean_inc(v_a_3570_);
lean_dec_ref(v___x_3569_);
v___x_3571_ = ((lean_object*)(l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termZoned_x28___x29__1___closed__0));
v___x_3572_ = lean_string_append(v___x_3571_, v_a_3570_);
lean_dec(v_a_3570_);
v___x_3573_ = l_Lean_Macro_throwErrorAt___redArg(v_offset_3563_, v___x_3572_, v_a_3556_, v_a_3557_);
lean_dec(v_offset_3563_);
return v___x_3573_;
}
else
{
lean_object* v_a_3574_; lean_object* v___x_3575_; lean_object* v_a_3576_; lean_object* v_a_3577_; lean_object* v___x_3579_; uint8_t v_isShared_3580_; uint8_t v_isSharedCheck_3584_; 
lean_dec(v_offset_3563_);
v_a_3574_ = lean_ctor_get(v___x_3569_, 0);
lean_inc(v_a_3574_);
lean_dec_ref(v___x_3569_);
lean_inc_ref(v_a_3556_);
v___x_3575_ = l___private_Std_Time_Notation_0__Std_Time_convertOffset(v_a_3574_, v_a_3556_, v_a_3557_);
lean_dec(v_a_3574_);
v_a_3576_ = lean_ctor_get(v___x_3575_, 0);
v_a_3577_ = lean_ctor_get(v___x_3575_, 1);
v_isSharedCheck_3584_ = !lean_is_exclusive(v___x_3575_);
if (v_isSharedCheck_3584_ == 0)
{
v___x_3579_ = v___x_3575_;
v_isShared_3580_ = v_isSharedCheck_3584_;
goto v_resetjp_3578_;
}
else
{
lean_inc(v_a_3577_);
lean_inc(v_a_3576_);
lean_dec(v___x_3575_);
v___x_3579_ = lean_box(0);
v_isShared_3580_ = v_isSharedCheck_3584_;
goto v_resetjp_3578_;
}
v_resetjp_3578_:
{
lean_object* v___x_3582_; 
if (v_isShared_3580_ == 0)
{
v___x_3582_ = v___x_3579_;
goto v_reusejp_3581_;
}
else
{
lean_object* v_reuseFailAlloc_3583_; 
v_reuseFailAlloc_3583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3583_, 0, v_a_3576_);
lean_ctor_set(v_reuseFailAlloc_3583_, 1, v_a_3577_);
v___x_3582_ = v_reuseFailAlloc_3583_;
goto v_reusejp_3581_;
}
v_reusejp_3581_:
{
return v___x_3582_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termOffset_x28___x29__1___boxed(lean_object* v_x_3585_, lean_object* v_a_3586_, lean_object* v_a_3587_){
_start:
{
lean_object* v_res_3588_; 
v_res_3588_ = l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termOffset_x28___x29__1(v_x_3585_, v_a_3586_, v_a_3587_);
lean_dec_ref(v_a_3586_);
return v_res_3588_;
}
}
LEAN_EXPORT lean_object* l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termTimezone_x28___x29__1(lean_object* v_x_3589_, lean_object* v_a_3590_, lean_object* v_a_3591_){
_start:
{
lean_object* v___x_3592_; uint8_t v___x_3593_; 
v___x_3592_ = ((lean_object*)(l_Std_Time_termTimezone_x28___x29___closed__1));
lean_inc(v_x_3589_);
v___x_3593_ = l_Lean_Syntax_isOfKind(v_x_3589_, v___x_3592_);
if (v___x_3593_ == 0)
{
lean_object* v___x_3594_; lean_object* v___x_3595_; 
lean_dec(v_x_3589_);
v___x_3594_ = lean_box(1);
v___x_3595_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3595_, 0, v___x_3594_);
lean_ctor_set(v___x_3595_, 1, v_a_3591_);
return v___x_3595_;
}
else
{
lean_object* v___x_3596_; lean_object* v_tz_3597_; lean_object* v___x_3598_; uint8_t v___x_3599_; 
v___x_3596_ = lean_unsigned_to_nat(1u);
v_tz_3597_ = l_Lean_Syntax_getArg(v_x_3589_, v___x_3596_);
lean_dec(v_x_3589_);
v___x_3598_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxString___closed__1));
lean_inc(v_tz_3597_);
v___x_3599_ = l_Lean_Syntax_isOfKind(v_tz_3597_, v___x_3598_);
if (v___x_3599_ == 0)
{
lean_object* v___x_3600_; lean_object* v___x_3601_; 
lean_dec(v_tz_3597_);
v___x_3600_ = lean_box(1);
v___x_3601_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3601_, 0, v___x_3600_);
lean_ctor_set(v___x_3601_, 1, v_a_3591_);
return v___x_3601_;
}
else
{
lean_object* v___x_3602_; lean_object* v___x_3603_; 
v___x_3602_ = l_Lean_TSyntax_getString(v_tz_3597_);
v___x_3603_ = l_Std_Time_TimeZone_fromTimeZone(v___x_3602_);
if (lean_obj_tag(v___x_3603_) == 0)
{
lean_object* v_a_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; 
v_a_3604_ = lean_ctor_get(v___x_3603_, 0);
lean_inc(v_a_3604_);
lean_dec_ref(v___x_3603_);
v___x_3605_ = ((lean_object*)(l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termZoned_x28___x29__1___closed__0));
v___x_3606_ = lean_string_append(v___x_3605_, v_a_3604_);
lean_dec(v_a_3604_);
v___x_3607_ = l_Lean_Macro_throwErrorAt___redArg(v_tz_3597_, v___x_3606_, v_a_3590_, v_a_3591_);
lean_dec(v_tz_3597_);
return v___x_3607_;
}
else
{
lean_object* v_a_3608_; lean_object* v___x_3609_; lean_object* v_a_3610_; lean_object* v_a_3611_; lean_object* v___x_3613_; uint8_t v_isShared_3614_; uint8_t v_isSharedCheck_3618_; 
lean_dec(v_tz_3597_);
v_a_3608_ = lean_ctor_get(v___x_3603_, 0);
lean_inc(v_a_3608_);
lean_dec_ref(v___x_3603_);
lean_inc_ref(v_a_3590_);
v___x_3609_ = l___private_Std_Time_Notation_0__Std_Time_convertTimezone(v_a_3608_, v_a_3590_, v_a_3591_);
v_a_3610_ = lean_ctor_get(v___x_3609_, 0);
v_a_3611_ = lean_ctor_get(v___x_3609_, 1);
v_isSharedCheck_3618_ = !lean_is_exclusive(v___x_3609_);
if (v_isSharedCheck_3618_ == 0)
{
v___x_3613_ = v___x_3609_;
v_isShared_3614_ = v_isSharedCheck_3618_;
goto v_resetjp_3612_;
}
else
{
lean_inc(v_a_3611_);
lean_inc(v_a_3610_);
lean_dec(v___x_3609_);
v___x_3613_ = lean_box(0);
v_isShared_3614_ = v_isSharedCheck_3618_;
goto v_resetjp_3612_;
}
v_resetjp_3612_:
{
lean_object* v___x_3616_; 
if (v_isShared_3614_ == 0)
{
v___x_3616_ = v___x_3613_;
goto v_reusejp_3615_;
}
else
{
lean_object* v_reuseFailAlloc_3617_; 
v_reuseFailAlloc_3617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3617_, 0, v_a_3610_);
lean_ctor_set(v_reuseFailAlloc_3617_, 1, v_a_3611_);
v___x_3616_ = v_reuseFailAlloc_3617_;
goto v_reusejp_3615_;
}
v_reusejp_3615_:
{
return v___x_3616_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termTimezone_x28___x29__1___boxed(lean_object* v_x_3619_, lean_object* v_a_3620_, lean_object* v_a_3621_){
_start:
{
lean_object* v_res_3622_; 
v_res_3622_ = l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termTimezone_x28___x29__1(v_x_3619_, v_a_3620_, v_a_3621_);
lean_dec_ref(v_a_3620_);
return v_res_3622_;
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

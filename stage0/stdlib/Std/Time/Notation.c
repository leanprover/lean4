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
uint8_t v_x_4038__boxed_103_; lean_object* v_res_104_; 
v_x_4038__boxed_103_ = lean_unbox(v_x_100_);
v_res_104_ = l___private_Std_Time_Notation_0__Std_Time_convertText(v_x_4038__boxed_103_, v_a_101_, v_a_102_);
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
lean_dec_ref(v_x_204_);
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
lean_dec_ref(v_x_322_);
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
uint8_t v_x_2693__boxed_448_; lean_object* v_res_449_; 
v_x_2693__boxed_448_ = lean_unbox(v_x_445_);
v_res_449_ = l___private_Std_Time_Notation_0__Std_Time_convertZoneName(v_x_2693__boxed_448_, v_a_446_, v_a_447_);
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
uint8_t v_x_6718__boxed_612_; lean_object* v_res_613_; 
v_x_6718__boxed_612_ = lean_unbox(v_x_609_);
v_res_613_ = l___private_Std_Time_Notation_0__Std_Time_convertOffsetX(v_x_6718__boxed_612_, v_a_610_, v_a_611_);
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
uint8_t v_x_2693__boxed_681_; lean_object* v_res_682_; 
v_x_2693__boxed_681_ = lean_unbox(v_x_678_);
v_res_682_ = l___private_Std_Time_Notation_0__Std_Time_convertOffsetO(v_x_2693__boxed_681_, v_a_679_, v_a_680_);
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
uint8_t v_x_4033__boxed_780_; lean_object* v_res_781_; 
v_x_4033__boxed_780_ = lean_unbox(v_x_777_);
v_res_781_ = l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ(v_x_4033__boxed_780_, v_a_778_, v_a_779_);
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
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49(void){
_start:
{
lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_900_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__48));
v___x_901_ = l_String_toRawSubstring_x27(v___x_900_);
return v___x_901_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__70(void){
_start:
{
lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_950_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__69));
v___x_951_ = l_String_toRawSubstring_x27(v___x_950_);
return v___x_951_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__74(void){
_start:
{
lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_956_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__73));
v___x_957_ = l_String_toRawSubstring_x27(v___x_956_);
return v___x_957_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__77(void){
_start:
{
lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_961_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__76));
v___x_962_ = l_String_toRawSubstring_x27(v___x_961_);
return v___x_962_;
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
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier(lean_object* v_x_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_){
_start:
{
switch(lean_obj_tag(v_x_1440_))
{
case 0:
{
uint8_t v_presentation_1443_; lean_object* v___x_1444_; lean_object* v_a_1445_; lean_object* v_a_1446_; lean_object* v___x_1448_; uint8_t v_isShared_1449_; uint8_t v_isSharedCheck_1467_; 
v_presentation_1443_ = lean_ctor_get_uint8(v_x_1440_, 0);
lean_dec_ref(v_x_1440_);
v___x_1444_ = l___private_Std_Time_Notation_0__Std_Time_convertText(v_presentation_1443_, v_a_1441_, v_a_1442_);
v_a_1445_ = lean_ctor_get(v___x_1444_, 0);
v_a_1446_ = lean_ctor_get(v___x_1444_, 1);
v_isSharedCheck_1467_ = !lean_is_exclusive(v___x_1444_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1448_ = v___x_1444_;
v_isShared_1449_ = v_isSharedCheck_1467_;
goto v_resetjp_1447_;
}
else
{
lean_inc(v_a_1446_);
lean_inc(v_a_1445_);
lean_dec(v___x_1444_);
v___x_1448_ = lean_box(0);
v_isShared_1449_ = v_isSharedCheck_1467_;
goto v_resetjp_1447_;
}
v_resetjp_1447_:
{
lean_object* v_quotContext_1450_; lean_object* v_currMacroScope_1451_; lean_object* v_ref_1452_; uint8_t v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1465_; 
v_quotContext_1450_ = lean_ctor_get(v_a_1441_, 1);
v_currMacroScope_1451_ = lean_ctor_get(v_a_1441_, 2);
v_ref_1452_ = lean_ctor_get(v_a_1441_, 5);
v___x_1453_ = 0;
v___x_1454_ = l_Lean_SourceInfo_fromRef(v_ref_1452_, v___x_1453_);
v___x_1455_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_1456_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__1, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__1_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__1);
v___x_1457_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__4));
lean_inc(v_currMacroScope_1451_);
lean_inc(v_quotContext_1450_);
v___x_1458_ = l_Lean_addMacroScope(v_quotContext_1450_, v___x_1457_, v_currMacroScope_1451_);
v___x_1459_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__8));
lean_inc_n(v___x_1454_, 2);
v___x_1460_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1460_, 0, v___x_1454_);
lean_ctor_set(v___x_1460_, 1, v___x_1456_);
lean_ctor_set(v___x_1460_, 2, v___x_1458_);
lean_ctor_set(v___x_1460_, 3, v___x_1459_);
v___x_1461_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_1462_ = l_Lean_Syntax_node1(v___x_1454_, v___x_1461_, v_a_1445_);
v___x_1463_ = l_Lean_Syntax_node2(v___x_1454_, v___x_1455_, v___x_1460_, v___x_1462_);
if (v_isShared_1449_ == 0)
{
lean_ctor_set(v___x_1448_, 0, v___x_1463_);
v___x_1465_ = v___x_1448_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v___x_1463_);
lean_ctor_set(v_reuseFailAlloc_1466_, 1, v_a_1446_);
v___x_1465_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
return v___x_1465_;
}
}
}
case 1:
{
lean_object* v_presentation_1468_; lean_object* v___x_1469_; lean_object* v_a_1470_; lean_object* v_a_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1492_; 
v_presentation_1468_ = lean_ctor_get(v_x_1440_, 0);
lean_inc(v_presentation_1468_);
lean_dec_ref(v_x_1440_);
v___x_1469_ = l___private_Std_Time_Notation_0__Std_Time_convertYear(v_presentation_1468_, v_a_1441_, v_a_1442_);
v_a_1470_ = lean_ctor_get(v___x_1469_, 0);
v_a_1471_ = lean_ctor_get(v___x_1469_, 1);
v_isSharedCheck_1492_ = !lean_is_exclusive(v___x_1469_);
if (v_isSharedCheck_1492_ == 0)
{
v___x_1473_ = v___x_1469_;
v_isShared_1474_ = v_isSharedCheck_1492_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_a_1471_);
lean_inc(v_a_1470_);
lean_dec(v___x_1469_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1492_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v_quotContext_1475_; lean_object* v_currMacroScope_1476_; lean_object* v_ref_1477_; uint8_t v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1490_; 
v_quotContext_1475_ = lean_ctor_get(v_a_1441_, 1);
v_currMacroScope_1476_ = lean_ctor_get(v_a_1441_, 2);
v_ref_1477_ = lean_ctor_get(v_a_1441_, 5);
v___x_1478_ = 0;
v___x_1479_ = l_Lean_SourceInfo_fromRef(v_ref_1477_, v___x_1478_);
v___x_1480_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_1481_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__10, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__10_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__10);
v___x_1482_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__12));
lean_inc(v_currMacroScope_1476_);
lean_inc(v_quotContext_1475_);
v___x_1483_ = l_Lean_addMacroScope(v_quotContext_1475_, v___x_1482_, v_currMacroScope_1476_);
v___x_1484_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__16));
lean_inc_n(v___x_1479_, 2);
v___x_1485_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1485_, 0, v___x_1479_);
lean_ctor_set(v___x_1485_, 1, v___x_1481_);
lean_ctor_set(v___x_1485_, 2, v___x_1483_);
lean_ctor_set(v___x_1485_, 3, v___x_1484_);
v___x_1486_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_1487_ = l_Lean_Syntax_node1(v___x_1479_, v___x_1486_, v_a_1470_);
v___x_1488_ = l_Lean_Syntax_node2(v___x_1479_, v___x_1480_, v___x_1485_, v___x_1487_);
if (v_isShared_1474_ == 0)
{
lean_ctor_set(v___x_1473_, 0, v___x_1488_);
v___x_1490_ = v___x_1473_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v___x_1488_);
lean_ctor_set(v_reuseFailAlloc_1491_, 1, v_a_1471_);
v___x_1490_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
return v___x_1490_;
}
}
}
case 2:
{
lean_object* v_presentation_1493_; lean_object* v___x_1494_; lean_object* v_a_1495_; lean_object* v_a_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1517_; 
v_presentation_1493_ = lean_ctor_get(v_x_1440_, 0);
lean_inc(v_presentation_1493_);
lean_dec_ref(v_x_1440_);
v___x_1494_ = l___private_Std_Time_Notation_0__Std_Time_convertYear(v_presentation_1493_, v_a_1441_, v_a_1442_);
v_a_1495_ = lean_ctor_get(v___x_1494_, 0);
v_a_1496_ = lean_ctor_get(v___x_1494_, 1);
v_isSharedCheck_1517_ = !lean_is_exclusive(v___x_1494_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1498_ = v___x_1494_;
v_isShared_1499_ = v_isSharedCheck_1517_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_a_1496_);
lean_inc(v_a_1495_);
lean_dec(v___x_1494_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1517_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v_quotContext_1500_; lean_object* v_currMacroScope_1501_; lean_object* v_ref_1502_; uint8_t v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1515_; 
v_quotContext_1500_ = lean_ctor_get(v_a_1441_, 1);
v_currMacroScope_1501_ = lean_ctor_get(v_a_1441_, 2);
v_ref_1502_ = lean_ctor_get(v_a_1441_, 5);
v___x_1503_ = 0;
v___x_1504_ = l_Lean_SourceInfo_fromRef(v_ref_1502_, v___x_1503_);
v___x_1505_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_1506_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__18, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__18_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__18);
v___x_1507_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__20));
lean_inc(v_currMacroScope_1501_);
lean_inc(v_quotContext_1500_);
v___x_1508_ = l_Lean_addMacroScope(v_quotContext_1500_, v___x_1507_, v_currMacroScope_1501_);
v___x_1509_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__24));
lean_inc_n(v___x_1504_, 2);
v___x_1510_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1510_, 0, v___x_1504_);
lean_ctor_set(v___x_1510_, 1, v___x_1506_);
lean_ctor_set(v___x_1510_, 2, v___x_1508_);
lean_ctor_set(v___x_1510_, 3, v___x_1509_);
v___x_1511_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_1512_ = l_Lean_Syntax_node1(v___x_1504_, v___x_1511_, v_a_1495_);
v___x_1513_ = l_Lean_Syntax_node2(v___x_1504_, v___x_1505_, v___x_1510_, v___x_1512_);
if (v_isShared_1499_ == 0)
{
lean_ctor_set(v___x_1498_, 0, v___x_1513_);
v___x_1515_ = v___x_1498_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v___x_1513_);
lean_ctor_set(v_reuseFailAlloc_1516_, 1, v_a_1496_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
return v___x_1515_;
}
}
}
case 3:
{
lean_object* v_presentation_1518_; lean_object* v___x_1519_; lean_object* v_a_1520_; lean_object* v_a_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1542_; 
v_presentation_1518_ = lean_ctor_get(v_x_1440_, 0);
lean_inc(v_presentation_1518_);
lean_dec_ref(v_x_1440_);
v___x_1519_ = l___private_Std_Time_Notation_0__Std_Time_convertNumber(v_presentation_1518_, v_a_1441_, v_a_1442_);
v_a_1520_ = lean_ctor_get(v___x_1519_, 0);
v_a_1521_ = lean_ctor_get(v___x_1519_, 1);
v_isSharedCheck_1542_ = !lean_is_exclusive(v___x_1519_);
if (v_isSharedCheck_1542_ == 0)
{
v___x_1523_ = v___x_1519_;
v_isShared_1524_ = v_isSharedCheck_1542_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_a_1521_);
lean_inc(v_a_1520_);
lean_dec(v___x_1519_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1542_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
lean_object* v_quotContext_1525_; lean_object* v_currMacroScope_1526_; lean_object* v_ref_1527_; uint8_t v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1540_; 
v_quotContext_1525_ = lean_ctor_get(v_a_1441_, 1);
v_currMacroScope_1526_ = lean_ctor_get(v_a_1441_, 2);
v_ref_1527_ = lean_ctor_get(v_a_1441_, 5);
v___x_1528_ = 0;
v___x_1529_ = l_Lean_SourceInfo_fromRef(v_ref_1527_, v___x_1528_);
v___x_1530_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_1531_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__26, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__26_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__26);
v___x_1532_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__28));
lean_inc(v_currMacroScope_1526_);
lean_inc(v_quotContext_1525_);
v___x_1533_ = l_Lean_addMacroScope(v_quotContext_1525_, v___x_1532_, v_currMacroScope_1526_);
v___x_1534_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__32));
lean_inc_n(v___x_1529_, 2);
v___x_1535_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1535_, 0, v___x_1529_);
lean_ctor_set(v___x_1535_, 1, v___x_1531_);
lean_ctor_set(v___x_1535_, 2, v___x_1533_);
lean_ctor_set(v___x_1535_, 3, v___x_1534_);
v___x_1536_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_1537_ = l_Lean_Syntax_node1(v___x_1529_, v___x_1536_, v_a_1520_);
v___x_1538_ = l_Lean_Syntax_node2(v___x_1529_, v___x_1530_, v___x_1535_, v___x_1537_);
if (v_isShared_1524_ == 0)
{
lean_ctor_set(v___x_1523_, 0, v___x_1538_);
v___x_1540_ = v___x_1523_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v___x_1538_);
lean_ctor_set(v_reuseFailAlloc_1541_, 1, v_a_1521_);
v___x_1540_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
return v___x_1540_;
}
}
}
case 4:
{
lean_object* v_presentation_1543_; 
v_presentation_1543_ = lean_ctor_get(v_x_1440_, 0);
lean_inc_ref(v_presentation_1543_);
lean_dec_ref(v_x_1440_);
if (lean_obj_tag(v_presentation_1543_) == 0)
{
lean_object* v_val_1544_; lean_object* v___x_1545_; lean_object* v_a_1546_; lean_object* v_a_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1594_; 
v_val_1544_ = lean_ctor_get(v_presentation_1543_, 0);
lean_inc(v_val_1544_);
lean_dec_ref(v_presentation_1543_);
v___x_1545_ = l___private_Std_Time_Notation_0__Std_Time_convertNumber(v_val_1544_, v_a_1441_, v_a_1442_);
v_a_1546_ = lean_ctor_get(v___x_1545_, 0);
v_a_1547_ = lean_ctor_get(v___x_1545_, 1);
v_isSharedCheck_1594_ = !lean_is_exclusive(v___x_1545_);
if (v_isSharedCheck_1594_ == 0)
{
v___x_1549_ = v___x_1545_;
v_isShared_1550_ = v_isSharedCheck_1594_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_a_1547_);
lean_inc(v_a_1546_);
lean_dec(v___x_1545_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1594_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v_quotContext_1551_; lean_object* v_currMacroScope_1552_; lean_object* v_ref_1553_; uint8_t v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1592_; 
v_quotContext_1551_ = lean_ctor_get(v_a_1441_, 1);
v_currMacroScope_1552_ = lean_ctor_get(v_a_1441_, 2);
v_ref_1553_ = lean_ctor_get(v_a_1441_, 5);
v___x_1554_ = 0;
v___x_1555_ = l_Lean_SourceInfo_fromRef(v_ref_1553_, v___x_1554_);
v___x_1556_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_1557_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__34, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__34_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__34);
v___x_1558_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__36));
lean_inc_n(v_currMacroScope_1552_, 3);
lean_inc_n(v_quotContext_1551_, 3);
v___x_1559_ = l_Lean_addMacroScope(v_quotContext_1551_, v___x_1558_, v_currMacroScope_1552_);
v___x_1560_ = lean_box(0);
v___x_1561_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__40));
lean_inc_n(v___x_1555_, 13);
v___x_1562_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1562_, 0, v___x_1555_);
lean_ctor_set(v___x_1562_, 1, v___x_1557_);
lean_ctor_set(v___x_1562_, 2, v___x_1559_);
lean_ctor_set(v___x_1562_, 3, v___x_1561_);
v___x_1563_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_1564_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__42));
v___x_1565_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__44));
v___x_1566_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__45));
v___x_1567_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1567_, 0, v___x_1555_);
lean_ctor_set(v___x_1567_, 1, v___x_1566_);
v___x_1568_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__47));
v___x_1569_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49);
v___x_1570_ = lean_box(0);
v___x_1571_ = l_Lean_addMacroScope(v_quotContext_1551_, v___x_1570_, v_currMacroScope_1552_);
v___x_1572_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__65));
v___x_1573_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1573_, 0, v___x_1555_);
lean_ctor_set(v___x_1573_, 1, v___x_1569_);
lean_ctor_set(v___x_1573_, 2, v___x_1571_);
lean_ctor_set(v___x_1573_, 3, v___x_1572_);
v___x_1574_ = l_Lean_Syntax_node1(v___x_1555_, v___x_1568_, v___x_1573_);
v___x_1575_ = l_Lean_Syntax_node2(v___x_1555_, v___x_1565_, v___x_1567_, v___x_1574_);
v___x_1576_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__67));
v___x_1577_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__68));
v___x_1578_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1578_, 0, v___x_1555_);
lean_ctor_set(v___x_1578_, 1, v___x_1577_);
v___x_1579_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__70, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__70_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__70);
v___x_1580_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__71));
v___x_1581_ = l_Lean_addMacroScope(v_quotContext_1551_, v___x_1580_, v_currMacroScope_1552_);
v___x_1582_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1582_, 0, v___x_1555_);
lean_ctor_set(v___x_1582_, 1, v___x_1579_);
lean_ctor_set(v___x_1582_, 2, v___x_1581_);
lean_ctor_set(v___x_1582_, 3, v___x_1560_);
v___x_1583_ = l_Lean_Syntax_node2(v___x_1555_, v___x_1576_, v___x_1578_, v___x_1582_);
v___x_1584_ = l_Lean_Syntax_node1(v___x_1555_, v___x_1563_, v_a_1546_);
v___x_1585_ = l_Lean_Syntax_node2(v___x_1555_, v___x_1556_, v___x_1583_, v___x_1584_);
v___x_1586_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__72));
v___x_1587_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1587_, 0, v___x_1555_);
lean_ctor_set(v___x_1587_, 1, v___x_1586_);
v___x_1588_ = l_Lean_Syntax_node3(v___x_1555_, v___x_1564_, v___x_1575_, v___x_1585_, v___x_1587_);
v___x_1589_ = l_Lean_Syntax_node1(v___x_1555_, v___x_1563_, v___x_1588_);
v___x_1590_ = l_Lean_Syntax_node2(v___x_1555_, v___x_1556_, v___x_1562_, v___x_1589_);
if (v_isShared_1550_ == 0)
{
lean_ctor_set(v___x_1549_, 0, v___x_1590_);
v___x_1592_ = v___x_1549_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v___x_1590_);
lean_ctor_set(v_reuseFailAlloc_1593_, 1, v_a_1547_);
v___x_1592_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
return v___x_1592_;
}
}
}
else
{
lean_object* v_val_1595_; uint8_t v___x_1596_; lean_object* v___x_1597_; lean_object* v_a_1598_; lean_object* v_a_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1646_; 
v_val_1595_ = lean_ctor_get(v_presentation_1543_, 0);
lean_inc(v_val_1595_);
lean_dec_ref(v_presentation_1543_);
v___x_1596_ = lean_unbox(v_val_1595_);
lean_dec(v_val_1595_);
v___x_1597_ = l___private_Std_Time_Notation_0__Std_Time_convertText(v___x_1596_, v_a_1441_, v_a_1442_);
v_a_1598_ = lean_ctor_get(v___x_1597_, 0);
v_a_1599_ = lean_ctor_get(v___x_1597_, 1);
v_isSharedCheck_1646_ = !lean_is_exclusive(v___x_1597_);
if (v_isSharedCheck_1646_ == 0)
{
v___x_1601_ = v___x_1597_;
v_isShared_1602_ = v_isSharedCheck_1646_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_a_1599_);
lean_inc(v_a_1598_);
lean_dec(v___x_1597_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1646_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v_quotContext_1603_; lean_object* v_currMacroScope_1604_; lean_object* v_ref_1605_; uint8_t v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1644_; 
v_quotContext_1603_ = lean_ctor_get(v_a_1441_, 1);
v_currMacroScope_1604_ = lean_ctor_get(v_a_1441_, 2);
v_ref_1605_ = lean_ctor_get(v_a_1441_, 5);
v___x_1606_ = 0;
v___x_1607_ = l_Lean_SourceInfo_fromRef(v_ref_1605_, v___x_1606_);
v___x_1608_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_1609_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__34, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__34_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__34);
v___x_1610_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__36));
lean_inc_n(v_currMacroScope_1604_, 3);
lean_inc_n(v_quotContext_1603_, 3);
v___x_1611_ = l_Lean_addMacroScope(v_quotContext_1603_, v___x_1610_, v_currMacroScope_1604_);
v___x_1612_ = lean_box(0);
v___x_1613_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__40));
lean_inc_n(v___x_1607_, 13);
v___x_1614_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1614_, 0, v___x_1607_);
lean_ctor_set(v___x_1614_, 1, v___x_1609_);
lean_ctor_set(v___x_1614_, 2, v___x_1611_);
lean_ctor_set(v___x_1614_, 3, v___x_1613_);
v___x_1615_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_1616_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__42));
v___x_1617_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__44));
v___x_1618_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__45));
v___x_1619_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1607_);
lean_ctor_set(v___x_1619_, 1, v___x_1618_);
v___x_1620_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__47));
v___x_1621_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49);
v___x_1622_ = lean_box(0);
v___x_1623_ = l_Lean_addMacroScope(v_quotContext_1603_, v___x_1622_, v_currMacroScope_1604_);
v___x_1624_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__65));
v___x_1625_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1607_);
lean_ctor_set(v___x_1625_, 1, v___x_1621_);
lean_ctor_set(v___x_1625_, 2, v___x_1623_);
lean_ctor_set(v___x_1625_, 3, v___x_1624_);
v___x_1626_ = l_Lean_Syntax_node1(v___x_1607_, v___x_1620_, v___x_1625_);
v___x_1627_ = l_Lean_Syntax_node2(v___x_1607_, v___x_1617_, v___x_1619_, v___x_1626_);
v___x_1628_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__67));
v___x_1629_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__68));
v___x_1630_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1630_, 0, v___x_1607_);
lean_ctor_set(v___x_1630_, 1, v___x_1629_);
v___x_1631_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__74, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__74_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__74);
v___x_1632_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__75));
v___x_1633_ = l_Lean_addMacroScope(v_quotContext_1603_, v___x_1632_, v_currMacroScope_1604_);
v___x_1634_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1634_, 0, v___x_1607_);
lean_ctor_set(v___x_1634_, 1, v___x_1631_);
lean_ctor_set(v___x_1634_, 2, v___x_1633_);
lean_ctor_set(v___x_1634_, 3, v___x_1612_);
v___x_1635_ = l_Lean_Syntax_node2(v___x_1607_, v___x_1628_, v___x_1630_, v___x_1634_);
v___x_1636_ = l_Lean_Syntax_node1(v___x_1607_, v___x_1615_, v_a_1598_);
v___x_1637_ = l_Lean_Syntax_node2(v___x_1607_, v___x_1608_, v___x_1635_, v___x_1636_);
v___x_1638_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__72));
v___x_1639_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1639_, 0, v___x_1607_);
lean_ctor_set(v___x_1639_, 1, v___x_1638_);
v___x_1640_ = l_Lean_Syntax_node3(v___x_1607_, v___x_1616_, v___x_1627_, v___x_1637_, v___x_1639_);
v___x_1641_ = l_Lean_Syntax_node1(v___x_1607_, v___x_1615_, v___x_1640_);
v___x_1642_ = l_Lean_Syntax_node2(v___x_1607_, v___x_1608_, v___x_1614_, v___x_1641_);
if (v_isShared_1602_ == 0)
{
lean_ctor_set(v___x_1601_, 0, v___x_1642_);
v___x_1644_ = v___x_1601_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v___x_1642_);
lean_ctor_set(v_reuseFailAlloc_1645_, 1, v_a_1599_);
v___x_1644_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
return v___x_1644_;
}
}
}
}
case 5:
{
lean_object* v_presentation_1647_; lean_object* v___x_1648_; lean_object* v_a_1649_; lean_object* v_a_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1671_; 
v_presentation_1647_ = lean_ctor_get(v_x_1440_, 0);
lean_inc(v_presentation_1647_);
lean_dec_ref(v_x_1440_);
v___x_1648_ = l___private_Std_Time_Notation_0__Std_Time_convertNumber(v_presentation_1647_, v_a_1441_, v_a_1442_);
v_a_1649_ = lean_ctor_get(v___x_1648_, 0);
v_a_1650_ = lean_ctor_get(v___x_1648_, 1);
v_isSharedCheck_1671_ = !lean_is_exclusive(v___x_1648_);
if (v_isSharedCheck_1671_ == 0)
{
v___x_1652_ = v___x_1648_;
v_isShared_1653_ = v_isSharedCheck_1671_;
goto v_resetjp_1651_;
}
else
{
lean_inc(v_a_1650_);
lean_inc(v_a_1649_);
lean_dec(v___x_1648_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1671_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v_quotContext_1654_; lean_object* v_currMacroScope_1655_; lean_object* v_ref_1656_; uint8_t v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1669_; 
v_quotContext_1654_ = lean_ctor_get(v_a_1441_, 1);
v_currMacroScope_1655_ = lean_ctor_get(v_a_1441_, 2);
v_ref_1656_ = lean_ctor_get(v_a_1441_, 5);
v___x_1657_ = 0;
v___x_1658_ = l_Lean_SourceInfo_fromRef(v_ref_1656_, v___x_1657_);
v___x_1659_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_1660_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__77, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__77_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__77);
v___x_1661_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__79));
lean_inc(v_currMacroScope_1655_);
lean_inc(v_quotContext_1654_);
v___x_1662_ = l_Lean_addMacroScope(v_quotContext_1654_, v___x_1661_, v_currMacroScope_1655_);
v___x_1663_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__83));
lean_inc_n(v___x_1658_, 2);
v___x_1664_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1664_, 0, v___x_1658_);
lean_ctor_set(v___x_1664_, 1, v___x_1660_);
lean_ctor_set(v___x_1664_, 2, v___x_1662_);
lean_ctor_set(v___x_1664_, 3, v___x_1663_);
v___x_1665_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_1666_ = l_Lean_Syntax_node1(v___x_1658_, v___x_1665_, v_a_1649_);
v___x_1667_ = l_Lean_Syntax_node2(v___x_1658_, v___x_1659_, v___x_1664_, v___x_1666_);
if (v_isShared_1653_ == 0)
{
lean_ctor_set(v___x_1652_, 0, v___x_1667_);
v___x_1669_ = v___x_1652_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v___x_1667_);
lean_ctor_set(v_reuseFailAlloc_1670_, 1, v_a_1650_);
v___x_1669_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
return v___x_1669_;
}
}
}
case 6:
{
lean_object* v_presentation_1672_; 
v_presentation_1672_ = lean_ctor_get(v_x_1440_, 0);
lean_inc_ref(v_presentation_1672_);
lean_dec_ref(v_x_1440_);
if (lean_obj_tag(v_presentation_1672_) == 0)
{
lean_object* v_val_1673_; lean_object* v___x_1674_; lean_object* v_a_1675_; lean_object* v_a_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1723_; 
v_val_1673_ = lean_ctor_get(v_presentation_1672_, 0);
lean_inc(v_val_1673_);
lean_dec_ref(v_presentation_1672_);
v___x_1674_ = l___private_Std_Time_Notation_0__Std_Time_convertNumber(v_val_1673_, v_a_1441_, v_a_1442_);
v_a_1675_ = lean_ctor_get(v___x_1674_, 0);
v_a_1676_ = lean_ctor_get(v___x_1674_, 1);
v_isSharedCheck_1723_ = !lean_is_exclusive(v___x_1674_);
if (v_isSharedCheck_1723_ == 0)
{
v___x_1678_ = v___x_1674_;
v_isShared_1679_ = v_isSharedCheck_1723_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_a_1676_);
lean_inc(v_a_1675_);
lean_dec(v___x_1674_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1723_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
lean_object* v_quotContext_1680_; lean_object* v_currMacroScope_1681_; lean_object* v_ref_1682_; uint8_t v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1721_; 
v_quotContext_1680_ = lean_ctor_get(v_a_1441_, 1);
v_currMacroScope_1681_ = lean_ctor_get(v_a_1441_, 2);
v_ref_1682_ = lean_ctor_get(v_a_1441_, 5);
v___x_1683_ = 0;
v___x_1684_ = l_Lean_SourceInfo_fromRef(v_ref_1682_, v___x_1683_);
v___x_1685_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_1686_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__85, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__85_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__85);
v___x_1687_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__87));
lean_inc_n(v_currMacroScope_1681_, 3);
lean_inc_n(v_quotContext_1680_, 3);
v___x_1688_ = l_Lean_addMacroScope(v_quotContext_1680_, v___x_1687_, v_currMacroScope_1681_);
v___x_1689_ = lean_box(0);
v___x_1690_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__91));
lean_inc_n(v___x_1684_, 13);
v___x_1691_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1691_, 0, v___x_1684_);
lean_ctor_set(v___x_1691_, 1, v___x_1686_);
lean_ctor_set(v___x_1691_, 2, v___x_1688_);
lean_ctor_set(v___x_1691_, 3, v___x_1690_);
v___x_1692_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_1693_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__42));
v___x_1694_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__44));
v___x_1695_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__45));
v___x_1696_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1696_, 0, v___x_1684_);
lean_ctor_set(v___x_1696_, 1, v___x_1695_);
v___x_1697_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__47));
v___x_1698_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49);
v___x_1699_ = lean_box(0);
v___x_1700_ = l_Lean_addMacroScope(v_quotContext_1680_, v___x_1699_, v_currMacroScope_1681_);
v___x_1701_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__65));
v___x_1702_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1702_, 0, v___x_1684_);
lean_ctor_set(v___x_1702_, 1, v___x_1698_);
lean_ctor_set(v___x_1702_, 2, v___x_1700_);
lean_ctor_set(v___x_1702_, 3, v___x_1701_);
v___x_1703_ = l_Lean_Syntax_node1(v___x_1684_, v___x_1697_, v___x_1702_);
v___x_1704_ = l_Lean_Syntax_node2(v___x_1684_, v___x_1694_, v___x_1696_, v___x_1703_);
v___x_1705_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__67));
v___x_1706_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__68));
v___x_1707_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1707_, 0, v___x_1684_);
lean_ctor_set(v___x_1707_, 1, v___x_1706_);
v___x_1708_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__70, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__70_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__70);
v___x_1709_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__71));
v___x_1710_ = l_Lean_addMacroScope(v_quotContext_1680_, v___x_1709_, v_currMacroScope_1681_);
v___x_1711_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1711_, 0, v___x_1684_);
lean_ctor_set(v___x_1711_, 1, v___x_1708_);
lean_ctor_set(v___x_1711_, 2, v___x_1710_);
lean_ctor_set(v___x_1711_, 3, v___x_1689_);
v___x_1712_ = l_Lean_Syntax_node2(v___x_1684_, v___x_1705_, v___x_1707_, v___x_1711_);
v___x_1713_ = l_Lean_Syntax_node1(v___x_1684_, v___x_1692_, v_a_1675_);
v___x_1714_ = l_Lean_Syntax_node2(v___x_1684_, v___x_1685_, v___x_1712_, v___x_1713_);
v___x_1715_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__72));
v___x_1716_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1716_, 0, v___x_1684_);
lean_ctor_set(v___x_1716_, 1, v___x_1715_);
v___x_1717_ = l_Lean_Syntax_node3(v___x_1684_, v___x_1693_, v___x_1704_, v___x_1714_, v___x_1716_);
v___x_1718_ = l_Lean_Syntax_node1(v___x_1684_, v___x_1692_, v___x_1717_);
v___x_1719_ = l_Lean_Syntax_node2(v___x_1684_, v___x_1685_, v___x_1691_, v___x_1718_);
if (v_isShared_1679_ == 0)
{
lean_ctor_set(v___x_1678_, 0, v___x_1719_);
v___x_1721_ = v___x_1678_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v___x_1719_);
lean_ctor_set(v_reuseFailAlloc_1722_, 1, v_a_1676_);
v___x_1721_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
return v___x_1721_;
}
}
}
else
{
lean_object* v_val_1724_; uint8_t v___x_1725_; lean_object* v___x_1726_; lean_object* v_a_1727_; lean_object* v_a_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1775_; 
v_val_1724_ = lean_ctor_get(v_presentation_1672_, 0);
lean_inc(v_val_1724_);
lean_dec_ref(v_presentation_1672_);
v___x_1725_ = lean_unbox(v_val_1724_);
lean_dec(v_val_1724_);
v___x_1726_ = l___private_Std_Time_Notation_0__Std_Time_convertText(v___x_1725_, v_a_1441_, v_a_1442_);
v_a_1727_ = lean_ctor_get(v___x_1726_, 0);
v_a_1728_ = lean_ctor_get(v___x_1726_, 1);
v_isSharedCheck_1775_ = !lean_is_exclusive(v___x_1726_);
if (v_isSharedCheck_1775_ == 0)
{
v___x_1730_ = v___x_1726_;
v_isShared_1731_ = v_isSharedCheck_1775_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_a_1728_);
lean_inc(v_a_1727_);
lean_dec(v___x_1726_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1775_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
lean_object* v_quotContext_1732_; lean_object* v_currMacroScope_1733_; lean_object* v_ref_1734_; uint8_t v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1773_; 
v_quotContext_1732_ = lean_ctor_get(v_a_1441_, 1);
v_currMacroScope_1733_ = lean_ctor_get(v_a_1441_, 2);
v_ref_1734_ = lean_ctor_get(v_a_1441_, 5);
v___x_1735_ = 0;
v___x_1736_ = l_Lean_SourceInfo_fromRef(v_ref_1734_, v___x_1735_);
v___x_1737_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_1738_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__85, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__85_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__85);
v___x_1739_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__87));
lean_inc_n(v_currMacroScope_1733_, 3);
lean_inc_n(v_quotContext_1732_, 3);
v___x_1740_ = l_Lean_addMacroScope(v_quotContext_1732_, v___x_1739_, v_currMacroScope_1733_);
v___x_1741_ = lean_box(0);
v___x_1742_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__91));
lean_inc_n(v___x_1736_, 13);
v___x_1743_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1743_, 0, v___x_1736_);
lean_ctor_set(v___x_1743_, 1, v___x_1738_);
lean_ctor_set(v___x_1743_, 2, v___x_1740_);
lean_ctor_set(v___x_1743_, 3, v___x_1742_);
v___x_1744_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_1745_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__42));
v___x_1746_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__44));
v___x_1747_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__45));
v___x_1748_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1748_, 0, v___x_1736_);
lean_ctor_set(v___x_1748_, 1, v___x_1747_);
v___x_1749_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__47));
v___x_1750_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49);
v___x_1751_ = lean_box(0);
v___x_1752_ = l_Lean_addMacroScope(v_quotContext_1732_, v___x_1751_, v_currMacroScope_1733_);
v___x_1753_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__65));
v___x_1754_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1754_, 0, v___x_1736_);
lean_ctor_set(v___x_1754_, 1, v___x_1750_);
lean_ctor_set(v___x_1754_, 2, v___x_1752_);
lean_ctor_set(v___x_1754_, 3, v___x_1753_);
v___x_1755_ = l_Lean_Syntax_node1(v___x_1736_, v___x_1749_, v___x_1754_);
v___x_1756_ = l_Lean_Syntax_node2(v___x_1736_, v___x_1746_, v___x_1748_, v___x_1755_);
v___x_1757_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__67));
v___x_1758_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__68));
v___x_1759_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1759_, 0, v___x_1736_);
lean_ctor_set(v___x_1759_, 1, v___x_1758_);
v___x_1760_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__74, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__74_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__74);
v___x_1761_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__75));
v___x_1762_ = l_Lean_addMacroScope(v_quotContext_1732_, v___x_1761_, v_currMacroScope_1733_);
v___x_1763_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1763_, 0, v___x_1736_);
lean_ctor_set(v___x_1763_, 1, v___x_1760_);
lean_ctor_set(v___x_1763_, 2, v___x_1762_);
lean_ctor_set(v___x_1763_, 3, v___x_1741_);
v___x_1764_ = l_Lean_Syntax_node2(v___x_1736_, v___x_1757_, v___x_1759_, v___x_1763_);
v___x_1765_ = l_Lean_Syntax_node1(v___x_1736_, v___x_1744_, v_a_1727_);
v___x_1766_ = l_Lean_Syntax_node2(v___x_1736_, v___x_1737_, v___x_1764_, v___x_1765_);
v___x_1767_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__72));
v___x_1768_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1768_, 0, v___x_1736_);
lean_ctor_set(v___x_1768_, 1, v___x_1767_);
v___x_1769_ = l_Lean_Syntax_node3(v___x_1736_, v___x_1745_, v___x_1756_, v___x_1766_, v___x_1768_);
v___x_1770_ = l_Lean_Syntax_node1(v___x_1736_, v___x_1744_, v___x_1769_);
v___x_1771_ = l_Lean_Syntax_node2(v___x_1736_, v___x_1737_, v___x_1743_, v___x_1770_);
if (v_isShared_1731_ == 0)
{
lean_ctor_set(v___x_1730_, 0, v___x_1771_);
v___x_1773_ = v___x_1730_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v___x_1771_);
lean_ctor_set(v_reuseFailAlloc_1774_, 1, v_a_1728_);
v___x_1773_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
return v___x_1773_;
}
}
}
}
case 7:
{
lean_object* v_presentation_1776_; lean_object* v___x_1777_; lean_object* v_a_1778_; lean_object* v_a_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1800_; 
v_presentation_1776_ = lean_ctor_get(v_x_1440_, 0);
lean_inc(v_presentation_1776_);
lean_dec_ref(v_x_1440_);
v___x_1777_ = l___private_Std_Time_Notation_0__Std_Time_convertNumber(v_presentation_1776_, v_a_1441_, v_a_1442_);
v_a_1778_ = lean_ctor_get(v___x_1777_, 0);
v_a_1779_ = lean_ctor_get(v___x_1777_, 1);
v_isSharedCheck_1800_ = !lean_is_exclusive(v___x_1777_);
if (v_isSharedCheck_1800_ == 0)
{
v___x_1781_ = v___x_1777_;
v_isShared_1782_ = v_isSharedCheck_1800_;
goto v_resetjp_1780_;
}
else
{
lean_inc(v_a_1779_);
lean_inc(v_a_1778_);
lean_dec(v___x_1777_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1800_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
lean_object* v_quotContext_1783_; lean_object* v_currMacroScope_1784_; lean_object* v_ref_1785_; uint8_t v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1798_; 
v_quotContext_1783_ = lean_ctor_get(v_a_1441_, 1);
v_currMacroScope_1784_ = lean_ctor_get(v_a_1441_, 2);
v_ref_1785_ = lean_ctor_get(v_a_1441_, 5);
v___x_1786_ = 0;
v___x_1787_ = l_Lean_SourceInfo_fromRef(v_ref_1785_, v___x_1786_);
v___x_1788_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_1789_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__93, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__93_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__93);
v___x_1790_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__95));
lean_inc(v_currMacroScope_1784_);
lean_inc(v_quotContext_1783_);
v___x_1791_ = l_Lean_addMacroScope(v_quotContext_1783_, v___x_1790_, v_currMacroScope_1784_);
v___x_1792_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__99));
lean_inc_n(v___x_1787_, 2);
v___x_1793_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1793_, 0, v___x_1787_);
lean_ctor_set(v___x_1793_, 1, v___x_1789_);
lean_ctor_set(v___x_1793_, 2, v___x_1791_);
lean_ctor_set(v___x_1793_, 3, v___x_1792_);
v___x_1794_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_1795_ = l_Lean_Syntax_node1(v___x_1787_, v___x_1794_, v_a_1778_);
v___x_1796_ = l_Lean_Syntax_node2(v___x_1787_, v___x_1788_, v___x_1793_, v___x_1795_);
if (v_isShared_1782_ == 0)
{
lean_ctor_set(v___x_1781_, 0, v___x_1796_);
v___x_1798_ = v___x_1781_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v___x_1796_);
lean_ctor_set(v_reuseFailAlloc_1799_, 1, v_a_1779_);
v___x_1798_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
return v___x_1798_;
}
}
}
case 8:
{
lean_object* v_presentation_1801_; lean_object* v___x_1802_; lean_object* v_a_1803_; lean_object* v_a_1804_; lean_object* v___x_1806_; uint8_t v_isShared_1807_; uint8_t v_isSharedCheck_1825_; 
v_presentation_1801_ = lean_ctor_get(v_x_1440_, 0);
lean_inc(v_presentation_1801_);
lean_dec_ref(v_x_1440_);
v___x_1802_ = l___private_Std_Time_Notation_0__Std_Time_convertNumber(v_presentation_1801_, v_a_1441_, v_a_1442_);
v_a_1803_ = lean_ctor_get(v___x_1802_, 0);
v_a_1804_ = lean_ctor_get(v___x_1802_, 1);
v_isSharedCheck_1825_ = !lean_is_exclusive(v___x_1802_);
if (v_isSharedCheck_1825_ == 0)
{
v___x_1806_ = v___x_1802_;
v_isShared_1807_ = v_isSharedCheck_1825_;
goto v_resetjp_1805_;
}
else
{
lean_inc(v_a_1804_);
lean_inc(v_a_1803_);
lean_dec(v___x_1802_);
v___x_1806_ = lean_box(0);
v_isShared_1807_ = v_isSharedCheck_1825_;
goto v_resetjp_1805_;
}
v_resetjp_1805_:
{
lean_object* v_quotContext_1808_; lean_object* v_currMacroScope_1809_; lean_object* v_ref_1810_; uint8_t v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1823_; 
v_quotContext_1808_ = lean_ctor_get(v_a_1441_, 1);
v_currMacroScope_1809_ = lean_ctor_get(v_a_1441_, 2);
v_ref_1810_ = lean_ctor_get(v_a_1441_, 5);
v___x_1811_ = 0;
v___x_1812_ = l_Lean_SourceInfo_fromRef(v_ref_1810_, v___x_1811_);
v___x_1813_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_1814_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__101, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__101_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__101);
v___x_1815_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__103));
lean_inc(v_currMacroScope_1809_);
lean_inc(v_quotContext_1808_);
v___x_1816_ = l_Lean_addMacroScope(v_quotContext_1808_, v___x_1815_, v_currMacroScope_1809_);
v___x_1817_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__107));
lean_inc_n(v___x_1812_, 2);
v___x_1818_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1818_, 0, v___x_1812_);
lean_ctor_set(v___x_1818_, 1, v___x_1814_);
lean_ctor_set(v___x_1818_, 2, v___x_1816_);
lean_ctor_set(v___x_1818_, 3, v___x_1817_);
v___x_1819_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_1820_ = l_Lean_Syntax_node1(v___x_1812_, v___x_1819_, v_a_1803_);
v___x_1821_ = l_Lean_Syntax_node2(v___x_1812_, v___x_1813_, v___x_1818_, v___x_1820_);
if (v_isShared_1807_ == 0)
{
lean_ctor_set(v___x_1806_, 0, v___x_1821_);
v___x_1823_ = v___x_1806_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v___x_1821_);
lean_ctor_set(v_reuseFailAlloc_1824_, 1, v_a_1804_);
v___x_1823_ = v_reuseFailAlloc_1824_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
return v___x_1823_;
}
}
}
case 9:
{
uint8_t v_presentation_1826_; lean_object* v___x_1827_; lean_object* v_a_1828_; lean_object* v_a_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1850_; 
v_presentation_1826_ = lean_ctor_get_uint8(v_x_1440_, 0);
lean_dec_ref(v_x_1440_);
v___x_1827_ = l___private_Std_Time_Notation_0__Std_Time_convertText(v_presentation_1826_, v_a_1441_, v_a_1442_);
v_a_1828_ = lean_ctor_get(v___x_1827_, 0);
v_a_1829_ = lean_ctor_get(v___x_1827_, 1);
v_isSharedCheck_1850_ = !lean_is_exclusive(v___x_1827_);
if (v_isSharedCheck_1850_ == 0)
{
v___x_1831_ = v___x_1827_;
v_isShared_1832_ = v_isSharedCheck_1850_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_a_1829_);
lean_inc(v_a_1828_);
lean_dec(v___x_1827_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1850_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v_quotContext_1833_; lean_object* v_currMacroScope_1834_; lean_object* v_ref_1835_; uint8_t v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1848_; 
v_quotContext_1833_ = lean_ctor_get(v_a_1441_, 1);
v_currMacroScope_1834_ = lean_ctor_get(v_a_1441_, 2);
v_ref_1835_ = lean_ctor_get(v_a_1441_, 5);
v___x_1836_ = 0;
v___x_1837_ = l_Lean_SourceInfo_fromRef(v_ref_1835_, v___x_1836_);
v___x_1838_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_1839_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__109, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__109_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__109);
v___x_1840_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__111));
lean_inc(v_currMacroScope_1834_);
lean_inc(v_quotContext_1833_);
v___x_1841_ = l_Lean_addMacroScope(v_quotContext_1833_, v___x_1840_, v_currMacroScope_1834_);
v___x_1842_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__115));
lean_inc_n(v___x_1837_, 2);
v___x_1843_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1843_, 0, v___x_1837_);
lean_ctor_set(v___x_1843_, 1, v___x_1839_);
lean_ctor_set(v___x_1843_, 2, v___x_1841_);
lean_ctor_set(v___x_1843_, 3, v___x_1842_);
v___x_1844_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_1845_ = l_Lean_Syntax_node1(v___x_1837_, v___x_1844_, v_a_1828_);
v___x_1846_ = l_Lean_Syntax_node2(v___x_1837_, v___x_1838_, v___x_1843_, v___x_1845_);
if (v_isShared_1832_ == 0)
{
lean_ctor_set(v___x_1831_, 0, v___x_1846_);
v___x_1848_ = v___x_1831_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v___x_1846_);
lean_ctor_set(v_reuseFailAlloc_1849_, 1, v_a_1829_);
v___x_1848_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
return v___x_1848_;
}
}
}
case 10:
{
lean_object* v_presentation_1851_; 
v_presentation_1851_ = lean_ctor_get(v_x_1440_, 0);
lean_inc_ref(v_presentation_1851_);
lean_dec_ref(v_x_1440_);
if (lean_obj_tag(v_presentation_1851_) == 0)
{
lean_object* v_val_1852_; lean_object* v___x_1853_; lean_object* v_a_1854_; lean_object* v_a_1855_; lean_object* v___x_1857_; uint8_t v_isShared_1858_; uint8_t v_isSharedCheck_1902_; 
v_val_1852_ = lean_ctor_get(v_presentation_1851_, 0);
lean_inc(v_val_1852_);
lean_dec_ref(v_presentation_1851_);
v___x_1853_ = l___private_Std_Time_Notation_0__Std_Time_convertNumber(v_val_1852_, v_a_1441_, v_a_1442_);
v_a_1854_ = lean_ctor_get(v___x_1853_, 0);
v_a_1855_ = lean_ctor_get(v___x_1853_, 1);
v_isSharedCheck_1902_ = !lean_is_exclusive(v___x_1853_);
if (v_isSharedCheck_1902_ == 0)
{
v___x_1857_ = v___x_1853_;
v_isShared_1858_ = v_isSharedCheck_1902_;
goto v_resetjp_1856_;
}
else
{
lean_inc(v_a_1855_);
lean_inc(v_a_1854_);
lean_dec(v___x_1853_);
v___x_1857_ = lean_box(0);
v_isShared_1858_ = v_isSharedCheck_1902_;
goto v_resetjp_1856_;
}
v_resetjp_1856_:
{
lean_object* v_quotContext_1859_; lean_object* v_currMacroScope_1860_; lean_object* v_ref_1861_; uint8_t v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1900_; 
v_quotContext_1859_ = lean_ctor_get(v_a_1441_, 1);
v_currMacroScope_1860_ = lean_ctor_get(v_a_1441_, 2);
v_ref_1861_ = lean_ctor_get(v_a_1441_, 5);
v___x_1862_ = 0;
v___x_1863_ = l_Lean_SourceInfo_fromRef(v_ref_1861_, v___x_1862_);
v___x_1864_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_1865_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__117, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__117_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__117);
v___x_1866_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__119));
lean_inc_n(v_currMacroScope_1860_, 3);
lean_inc_n(v_quotContext_1859_, 3);
v___x_1867_ = l_Lean_addMacroScope(v_quotContext_1859_, v___x_1866_, v_currMacroScope_1860_);
v___x_1868_ = lean_box(0);
v___x_1869_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__123));
lean_inc_n(v___x_1863_, 13);
v___x_1870_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1870_, 0, v___x_1863_);
lean_ctor_set(v___x_1870_, 1, v___x_1865_);
lean_ctor_set(v___x_1870_, 2, v___x_1867_);
lean_ctor_set(v___x_1870_, 3, v___x_1869_);
v___x_1871_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_1872_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__42));
v___x_1873_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__44));
v___x_1874_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__45));
v___x_1875_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1875_, 0, v___x_1863_);
lean_ctor_set(v___x_1875_, 1, v___x_1874_);
v___x_1876_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__47));
v___x_1877_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49);
v___x_1878_ = lean_box(0);
v___x_1879_ = l_Lean_addMacroScope(v_quotContext_1859_, v___x_1878_, v_currMacroScope_1860_);
v___x_1880_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__65));
v___x_1881_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1881_, 0, v___x_1863_);
lean_ctor_set(v___x_1881_, 1, v___x_1877_);
lean_ctor_set(v___x_1881_, 2, v___x_1879_);
lean_ctor_set(v___x_1881_, 3, v___x_1880_);
v___x_1882_ = l_Lean_Syntax_node1(v___x_1863_, v___x_1876_, v___x_1881_);
v___x_1883_ = l_Lean_Syntax_node2(v___x_1863_, v___x_1873_, v___x_1875_, v___x_1882_);
v___x_1884_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__67));
v___x_1885_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__68));
v___x_1886_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1886_, 0, v___x_1863_);
lean_ctor_set(v___x_1886_, 1, v___x_1885_);
v___x_1887_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__70, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__70_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__70);
v___x_1888_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__71));
v___x_1889_ = l_Lean_addMacroScope(v_quotContext_1859_, v___x_1888_, v_currMacroScope_1860_);
v___x_1890_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1890_, 0, v___x_1863_);
lean_ctor_set(v___x_1890_, 1, v___x_1887_);
lean_ctor_set(v___x_1890_, 2, v___x_1889_);
lean_ctor_set(v___x_1890_, 3, v___x_1868_);
v___x_1891_ = l_Lean_Syntax_node2(v___x_1863_, v___x_1884_, v___x_1886_, v___x_1890_);
v___x_1892_ = l_Lean_Syntax_node1(v___x_1863_, v___x_1871_, v_a_1854_);
v___x_1893_ = l_Lean_Syntax_node2(v___x_1863_, v___x_1864_, v___x_1891_, v___x_1892_);
v___x_1894_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__72));
v___x_1895_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1895_, 0, v___x_1863_);
lean_ctor_set(v___x_1895_, 1, v___x_1894_);
v___x_1896_ = l_Lean_Syntax_node3(v___x_1863_, v___x_1872_, v___x_1883_, v___x_1893_, v___x_1895_);
v___x_1897_ = l_Lean_Syntax_node1(v___x_1863_, v___x_1871_, v___x_1896_);
v___x_1898_ = l_Lean_Syntax_node2(v___x_1863_, v___x_1864_, v___x_1870_, v___x_1897_);
if (v_isShared_1858_ == 0)
{
lean_ctor_set(v___x_1857_, 0, v___x_1898_);
v___x_1900_ = v___x_1857_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v___x_1898_);
lean_ctor_set(v_reuseFailAlloc_1901_, 1, v_a_1855_);
v___x_1900_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
return v___x_1900_;
}
}
}
else
{
lean_object* v_val_1903_; uint8_t v___x_1904_; lean_object* v___x_1905_; lean_object* v_a_1906_; lean_object* v_a_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1954_; 
v_val_1903_ = lean_ctor_get(v_presentation_1851_, 0);
lean_inc(v_val_1903_);
lean_dec_ref(v_presentation_1851_);
v___x_1904_ = lean_unbox(v_val_1903_);
lean_dec(v_val_1903_);
v___x_1905_ = l___private_Std_Time_Notation_0__Std_Time_convertText(v___x_1904_, v_a_1441_, v_a_1442_);
v_a_1906_ = lean_ctor_get(v___x_1905_, 0);
v_a_1907_ = lean_ctor_get(v___x_1905_, 1);
v_isSharedCheck_1954_ = !lean_is_exclusive(v___x_1905_);
if (v_isSharedCheck_1954_ == 0)
{
v___x_1909_ = v___x_1905_;
v_isShared_1910_ = v_isSharedCheck_1954_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_a_1907_);
lean_inc(v_a_1906_);
lean_dec(v___x_1905_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1954_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
lean_object* v_quotContext_1911_; lean_object* v_currMacroScope_1912_; lean_object* v_ref_1913_; uint8_t v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1952_; 
v_quotContext_1911_ = lean_ctor_get(v_a_1441_, 1);
v_currMacroScope_1912_ = lean_ctor_get(v_a_1441_, 2);
v_ref_1913_ = lean_ctor_get(v_a_1441_, 5);
v___x_1914_ = 0;
v___x_1915_ = l_Lean_SourceInfo_fromRef(v_ref_1913_, v___x_1914_);
v___x_1916_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_1917_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__117, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__117_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__117);
v___x_1918_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__119));
lean_inc_n(v_currMacroScope_1912_, 3);
lean_inc_n(v_quotContext_1911_, 3);
v___x_1919_ = l_Lean_addMacroScope(v_quotContext_1911_, v___x_1918_, v_currMacroScope_1912_);
v___x_1920_ = lean_box(0);
v___x_1921_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__123));
lean_inc_n(v___x_1915_, 13);
v___x_1922_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1922_, 0, v___x_1915_);
lean_ctor_set(v___x_1922_, 1, v___x_1917_);
lean_ctor_set(v___x_1922_, 2, v___x_1919_);
lean_ctor_set(v___x_1922_, 3, v___x_1921_);
v___x_1923_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_1924_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__42));
v___x_1925_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__44));
v___x_1926_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__45));
v___x_1927_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1915_);
lean_ctor_set(v___x_1927_, 1, v___x_1926_);
v___x_1928_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__47));
v___x_1929_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49);
v___x_1930_ = lean_box(0);
v___x_1931_ = l_Lean_addMacroScope(v_quotContext_1911_, v___x_1930_, v_currMacroScope_1912_);
v___x_1932_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__65));
v___x_1933_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1933_, 0, v___x_1915_);
lean_ctor_set(v___x_1933_, 1, v___x_1929_);
lean_ctor_set(v___x_1933_, 2, v___x_1931_);
lean_ctor_set(v___x_1933_, 3, v___x_1932_);
v___x_1934_ = l_Lean_Syntax_node1(v___x_1915_, v___x_1928_, v___x_1933_);
v___x_1935_ = l_Lean_Syntax_node2(v___x_1915_, v___x_1925_, v___x_1927_, v___x_1934_);
v___x_1936_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__67));
v___x_1937_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__68));
v___x_1938_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1938_, 0, v___x_1915_);
lean_ctor_set(v___x_1938_, 1, v___x_1937_);
v___x_1939_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__74, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__74_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__74);
v___x_1940_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__75));
v___x_1941_ = l_Lean_addMacroScope(v_quotContext_1911_, v___x_1940_, v_currMacroScope_1912_);
v___x_1942_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1942_, 0, v___x_1915_);
lean_ctor_set(v___x_1942_, 1, v___x_1939_);
lean_ctor_set(v___x_1942_, 2, v___x_1941_);
lean_ctor_set(v___x_1942_, 3, v___x_1920_);
v___x_1943_ = l_Lean_Syntax_node2(v___x_1915_, v___x_1936_, v___x_1938_, v___x_1942_);
v___x_1944_ = l_Lean_Syntax_node1(v___x_1915_, v___x_1923_, v_a_1906_);
v___x_1945_ = l_Lean_Syntax_node2(v___x_1915_, v___x_1916_, v___x_1943_, v___x_1944_);
v___x_1946_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__72));
v___x_1947_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1947_, 0, v___x_1915_);
lean_ctor_set(v___x_1947_, 1, v___x_1946_);
v___x_1948_ = l_Lean_Syntax_node3(v___x_1915_, v___x_1924_, v___x_1935_, v___x_1945_, v___x_1947_);
v___x_1949_ = l_Lean_Syntax_node1(v___x_1915_, v___x_1923_, v___x_1948_);
v___x_1950_ = l_Lean_Syntax_node2(v___x_1915_, v___x_1916_, v___x_1922_, v___x_1949_);
if (v_isShared_1910_ == 0)
{
lean_ctor_set(v___x_1909_, 0, v___x_1950_);
v___x_1952_ = v___x_1909_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v___x_1950_);
lean_ctor_set(v_reuseFailAlloc_1953_, 1, v_a_1907_);
v___x_1952_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
return v___x_1952_;
}
}
}
}
case 11:
{
lean_object* v_presentation_1955_; lean_object* v___x_1956_; lean_object* v_a_1957_; lean_object* v_a_1958_; lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1979_; 
v_presentation_1955_ = lean_ctor_get(v_x_1440_, 0);
lean_inc(v_presentation_1955_);
lean_dec_ref(v_x_1440_);
v___x_1956_ = l___private_Std_Time_Notation_0__Std_Time_convertNumber(v_presentation_1955_, v_a_1441_, v_a_1442_);
v_a_1957_ = lean_ctor_get(v___x_1956_, 0);
v_a_1958_ = lean_ctor_get(v___x_1956_, 1);
v_isSharedCheck_1979_ = !lean_is_exclusive(v___x_1956_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1960_ = v___x_1956_;
v_isShared_1961_ = v_isSharedCheck_1979_;
goto v_resetjp_1959_;
}
else
{
lean_inc(v_a_1958_);
lean_inc(v_a_1957_);
lean_dec(v___x_1956_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_1979_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
lean_object* v_quotContext_1962_; lean_object* v_currMacroScope_1963_; lean_object* v_ref_1964_; uint8_t v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1977_; 
v_quotContext_1962_ = lean_ctor_get(v_a_1441_, 1);
v_currMacroScope_1963_ = lean_ctor_get(v_a_1441_, 2);
v_ref_1964_ = lean_ctor_get(v_a_1441_, 5);
v___x_1965_ = 0;
v___x_1966_ = l_Lean_SourceInfo_fromRef(v_ref_1964_, v___x_1965_);
v___x_1967_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_1968_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__125, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__125_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__125);
v___x_1969_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__127));
lean_inc(v_currMacroScope_1963_);
lean_inc(v_quotContext_1962_);
v___x_1970_ = l_Lean_addMacroScope(v_quotContext_1962_, v___x_1969_, v_currMacroScope_1963_);
v___x_1971_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__131));
lean_inc_n(v___x_1966_, 2);
v___x_1972_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1972_, 0, v___x_1966_);
lean_ctor_set(v___x_1972_, 1, v___x_1968_);
lean_ctor_set(v___x_1972_, 2, v___x_1970_);
lean_ctor_set(v___x_1972_, 3, v___x_1971_);
v___x_1973_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_1974_ = l_Lean_Syntax_node1(v___x_1966_, v___x_1973_, v_a_1957_);
v___x_1975_ = l_Lean_Syntax_node2(v___x_1966_, v___x_1967_, v___x_1972_, v___x_1974_);
if (v_isShared_1961_ == 0)
{
lean_ctor_set(v___x_1960_, 0, v___x_1975_);
v___x_1977_ = v___x_1960_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v___x_1975_);
lean_ctor_set(v_reuseFailAlloc_1978_, 1, v_a_1958_);
v___x_1977_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
return v___x_1977_;
}
}
}
case 12:
{
uint8_t v_presentation_1980_; lean_object* v___x_1981_; lean_object* v_a_1982_; lean_object* v_a_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_2004_; 
v_presentation_1980_ = lean_ctor_get_uint8(v_x_1440_, 0);
lean_dec_ref(v_x_1440_);
v___x_1981_ = l___private_Std_Time_Notation_0__Std_Time_convertText(v_presentation_1980_, v_a_1441_, v_a_1442_);
v_a_1982_ = lean_ctor_get(v___x_1981_, 0);
v_a_1983_ = lean_ctor_get(v___x_1981_, 1);
v_isSharedCheck_2004_ = !lean_is_exclusive(v___x_1981_);
if (v_isSharedCheck_2004_ == 0)
{
v___x_1985_ = v___x_1981_;
v_isShared_1986_ = v_isSharedCheck_2004_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_a_1983_);
lean_inc(v_a_1982_);
lean_dec(v___x_1981_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_2004_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v_quotContext_1987_; lean_object* v_currMacroScope_1988_; lean_object* v_ref_1989_; uint8_t v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2002_; 
v_quotContext_1987_ = lean_ctor_get(v_a_1441_, 1);
v_currMacroScope_1988_ = lean_ctor_get(v_a_1441_, 2);
v_ref_1989_ = lean_ctor_get(v_a_1441_, 5);
v___x_1990_ = 0;
v___x_1991_ = l_Lean_SourceInfo_fromRef(v_ref_1989_, v___x_1990_);
v___x_1992_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_1993_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__133, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__133_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__133);
v___x_1994_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__135));
lean_inc(v_currMacroScope_1988_);
lean_inc(v_quotContext_1987_);
v___x_1995_ = l_Lean_addMacroScope(v_quotContext_1987_, v___x_1994_, v_currMacroScope_1988_);
v___x_1996_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__139));
lean_inc_n(v___x_1991_, 2);
v___x_1997_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1997_, 0, v___x_1991_);
lean_ctor_set(v___x_1997_, 1, v___x_1993_);
lean_ctor_set(v___x_1997_, 2, v___x_1995_);
lean_ctor_set(v___x_1997_, 3, v___x_1996_);
v___x_1998_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_1999_ = l_Lean_Syntax_node1(v___x_1991_, v___x_1998_, v_a_1982_);
v___x_2000_ = l_Lean_Syntax_node2(v___x_1991_, v___x_1992_, v___x_1997_, v___x_1999_);
if (v_isShared_1986_ == 0)
{
lean_ctor_set(v___x_1985_, 0, v___x_2000_);
v___x_2002_ = v___x_1985_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v___x_2000_);
lean_ctor_set(v_reuseFailAlloc_2003_, 1, v_a_1983_);
v___x_2002_ = v_reuseFailAlloc_2003_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
return v___x_2002_;
}
}
}
case 13:
{
lean_object* v_presentation_2005_; lean_object* v___x_2006_; lean_object* v_a_2007_; lean_object* v_a_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2029_; 
v_presentation_2005_ = lean_ctor_get(v_x_1440_, 0);
lean_inc(v_presentation_2005_);
lean_dec_ref(v_x_1440_);
v___x_2006_ = l___private_Std_Time_Notation_0__Std_Time_convertNumber(v_presentation_2005_, v_a_1441_, v_a_1442_);
v_a_2007_ = lean_ctor_get(v___x_2006_, 0);
v_a_2008_ = lean_ctor_get(v___x_2006_, 1);
v_isSharedCheck_2029_ = !lean_is_exclusive(v___x_2006_);
if (v_isSharedCheck_2029_ == 0)
{
v___x_2010_ = v___x_2006_;
v_isShared_2011_ = v_isSharedCheck_2029_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_a_2008_);
lean_inc(v_a_2007_);
lean_dec(v___x_2006_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2029_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v_quotContext_2012_; lean_object* v_currMacroScope_2013_; lean_object* v_ref_2014_; uint8_t v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2027_; 
v_quotContext_2012_ = lean_ctor_get(v_a_1441_, 1);
v_currMacroScope_2013_ = lean_ctor_get(v_a_1441_, 2);
v_ref_2014_ = lean_ctor_get(v_a_1441_, 5);
v___x_2015_ = 0;
v___x_2016_ = l_Lean_SourceInfo_fromRef(v_ref_2014_, v___x_2015_);
v___x_2017_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2018_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__141, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__141_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__141);
v___x_2019_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__143));
lean_inc(v_currMacroScope_2013_);
lean_inc(v_quotContext_2012_);
v___x_2020_ = l_Lean_addMacroScope(v_quotContext_2012_, v___x_2019_, v_currMacroScope_2013_);
v___x_2021_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__147));
lean_inc_n(v___x_2016_, 2);
v___x_2022_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2022_, 0, v___x_2016_);
lean_ctor_set(v___x_2022_, 1, v___x_2018_);
lean_ctor_set(v___x_2022_, 2, v___x_2020_);
lean_ctor_set(v___x_2022_, 3, v___x_2021_);
v___x_2023_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2024_ = l_Lean_Syntax_node1(v___x_2016_, v___x_2023_, v_a_2007_);
v___x_2025_ = l_Lean_Syntax_node2(v___x_2016_, v___x_2017_, v___x_2022_, v___x_2024_);
if (v_isShared_2011_ == 0)
{
lean_ctor_set(v___x_2010_, 0, v___x_2025_);
v___x_2027_ = v___x_2010_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v___x_2025_);
lean_ctor_set(v_reuseFailAlloc_2028_, 1, v_a_2008_);
v___x_2027_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
return v___x_2027_;
}
}
}
case 14:
{
lean_object* v_presentation_2030_; lean_object* v___x_2031_; lean_object* v_a_2032_; lean_object* v_a_2033_; lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2054_; 
v_presentation_2030_ = lean_ctor_get(v_x_1440_, 0);
lean_inc(v_presentation_2030_);
lean_dec_ref(v_x_1440_);
v___x_2031_ = l___private_Std_Time_Notation_0__Std_Time_convertNumber(v_presentation_2030_, v_a_1441_, v_a_1442_);
v_a_2032_ = lean_ctor_get(v___x_2031_, 0);
v_a_2033_ = lean_ctor_get(v___x_2031_, 1);
v_isSharedCheck_2054_ = !lean_is_exclusive(v___x_2031_);
if (v_isSharedCheck_2054_ == 0)
{
v___x_2035_ = v___x_2031_;
v_isShared_2036_ = v_isSharedCheck_2054_;
goto v_resetjp_2034_;
}
else
{
lean_inc(v_a_2033_);
lean_inc(v_a_2032_);
lean_dec(v___x_2031_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2054_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
lean_object* v_quotContext_2037_; lean_object* v_currMacroScope_2038_; lean_object* v_ref_2039_; uint8_t v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2052_; 
v_quotContext_2037_ = lean_ctor_get(v_a_1441_, 1);
v_currMacroScope_2038_ = lean_ctor_get(v_a_1441_, 2);
v_ref_2039_ = lean_ctor_get(v_a_1441_, 5);
v___x_2040_ = 0;
v___x_2041_ = l_Lean_SourceInfo_fromRef(v_ref_2039_, v___x_2040_);
v___x_2042_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2043_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__149, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__149_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__149);
v___x_2044_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__151));
lean_inc(v_currMacroScope_2038_);
lean_inc(v_quotContext_2037_);
v___x_2045_ = l_Lean_addMacroScope(v_quotContext_2037_, v___x_2044_, v_currMacroScope_2038_);
v___x_2046_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__155));
lean_inc_n(v___x_2041_, 2);
v___x_2047_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2047_, 0, v___x_2041_);
lean_ctor_set(v___x_2047_, 1, v___x_2043_);
lean_ctor_set(v___x_2047_, 2, v___x_2045_);
lean_ctor_set(v___x_2047_, 3, v___x_2046_);
v___x_2048_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2049_ = l_Lean_Syntax_node1(v___x_2041_, v___x_2048_, v_a_2032_);
v___x_2050_ = l_Lean_Syntax_node2(v___x_2041_, v___x_2042_, v___x_2047_, v___x_2049_);
if (v_isShared_2036_ == 0)
{
lean_ctor_set(v___x_2035_, 0, v___x_2050_);
v___x_2052_ = v___x_2035_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v___x_2050_);
lean_ctor_set(v_reuseFailAlloc_2053_, 1, v_a_2033_);
v___x_2052_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
return v___x_2052_;
}
}
}
case 15:
{
lean_object* v_presentation_2055_; lean_object* v___x_2056_; lean_object* v_a_2057_; lean_object* v_a_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2079_; 
v_presentation_2055_ = lean_ctor_get(v_x_1440_, 0);
lean_inc(v_presentation_2055_);
lean_dec_ref(v_x_1440_);
v___x_2056_ = l___private_Std_Time_Notation_0__Std_Time_convertNumber(v_presentation_2055_, v_a_1441_, v_a_1442_);
v_a_2057_ = lean_ctor_get(v___x_2056_, 0);
v_a_2058_ = lean_ctor_get(v___x_2056_, 1);
v_isSharedCheck_2079_ = !lean_is_exclusive(v___x_2056_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2060_ = v___x_2056_;
v_isShared_2061_ = v_isSharedCheck_2079_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_a_2058_);
lean_inc(v_a_2057_);
lean_dec(v___x_2056_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2079_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
lean_object* v_quotContext_2062_; lean_object* v_currMacroScope_2063_; lean_object* v_ref_2064_; uint8_t v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2077_; 
v_quotContext_2062_ = lean_ctor_get(v_a_1441_, 1);
v_currMacroScope_2063_ = lean_ctor_get(v_a_1441_, 2);
v_ref_2064_ = lean_ctor_get(v_a_1441_, 5);
v___x_2065_ = 0;
v___x_2066_ = l_Lean_SourceInfo_fromRef(v_ref_2064_, v___x_2065_);
v___x_2067_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2068_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__157, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__157_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__157);
v___x_2069_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__159));
lean_inc(v_currMacroScope_2063_);
lean_inc(v_quotContext_2062_);
v___x_2070_ = l_Lean_addMacroScope(v_quotContext_2062_, v___x_2069_, v_currMacroScope_2063_);
v___x_2071_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__163));
lean_inc_n(v___x_2066_, 2);
v___x_2072_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2072_, 0, v___x_2066_);
lean_ctor_set(v___x_2072_, 1, v___x_2068_);
lean_ctor_set(v___x_2072_, 2, v___x_2070_);
lean_ctor_set(v___x_2072_, 3, v___x_2071_);
v___x_2073_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2074_ = l_Lean_Syntax_node1(v___x_2066_, v___x_2073_, v_a_2057_);
v___x_2075_ = l_Lean_Syntax_node2(v___x_2066_, v___x_2067_, v___x_2072_, v___x_2074_);
if (v_isShared_2061_ == 0)
{
lean_ctor_set(v___x_2060_, 0, v___x_2075_);
v___x_2077_ = v___x_2060_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v___x_2075_);
lean_ctor_set(v_reuseFailAlloc_2078_, 1, v_a_2058_);
v___x_2077_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
return v___x_2077_;
}
}
}
case 16:
{
lean_object* v_presentation_2080_; lean_object* v___x_2081_; lean_object* v_a_2082_; lean_object* v_a_2083_; lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2104_; 
v_presentation_2080_ = lean_ctor_get(v_x_1440_, 0);
lean_inc(v_presentation_2080_);
lean_dec_ref(v_x_1440_);
v___x_2081_ = l___private_Std_Time_Notation_0__Std_Time_convertNumber(v_presentation_2080_, v_a_1441_, v_a_1442_);
v_a_2082_ = lean_ctor_get(v___x_2081_, 0);
v_a_2083_ = lean_ctor_get(v___x_2081_, 1);
v_isSharedCheck_2104_ = !lean_is_exclusive(v___x_2081_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_2085_ = v___x_2081_;
v_isShared_2086_ = v_isSharedCheck_2104_;
goto v_resetjp_2084_;
}
else
{
lean_inc(v_a_2083_);
lean_inc(v_a_2082_);
lean_dec(v___x_2081_);
v___x_2085_ = lean_box(0);
v_isShared_2086_ = v_isSharedCheck_2104_;
goto v_resetjp_2084_;
}
v_resetjp_2084_:
{
lean_object* v_quotContext_2087_; lean_object* v_currMacroScope_2088_; lean_object* v_ref_2089_; uint8_t v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2102_; 
v_quotContext_2087_ = lean_ctor_get(v_a_1441_, 1);
v_currMacroScope_2088_ = lean_ctor_get(v_a_1441_, 2);
v_ref_2089_ = lean_ctor_get(v_a_1441_, 5);
v___x_2090_ = 0;
v___x_2091_ = l_Lean_SourceInfo_fromRef(v_ref_2089_, v___x_2090_);
v___x_2092_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2093_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__165, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__165_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__165);
v___x_2094_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__167));
lean_inc(v_currMacroScope_2088_);
lean_inc(v_quotContext_2087_);
v___x_2095_ = l_Lean_addMacroScope(v_quotContext_2087_, v___x_2094_, v_currMacroScope_2088_);
v___x_2096_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__171));
lean_inc_n(v___x_2091_, 2);
v___x_2097_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2097_, 0, v___x_2091_);
lean_ctor_set(v___x_2097_, 1, v___x_2093_);
lean_ctor_set(v___x_2097_, 2, v___x_2095_);
lean_ctor_set(v___x_2097_, 3, v___x_2096_);
v___x_2098_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2099_ = l_Lean_Syntax_node1(v___x_2091_, v___x_2098_, v_a_2082_);
v___x_2100_ = l_Lean_Syntax_node2(v___x_2091_, v___x_2092_, v___x_2097_, v___x_2099_);
if (v_isShared_2086_ == 0)
{
lean_ctor_set(v___x_2085_, 0, v___x_2100_);
v___x_2102_ = v___x_2085_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v___x_2100_);
lean_ctor_set(v_reuseFailAlloc_2103_, 1, v_a_2083_);
v___x_2102_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
return v___x_2102_;
}
}
}
case 17:
{
lean_object* v_presentation_2105_; lean_object* v___x_2106_; lean_object* v_a_2107_; lean_object* v_a_2108_; lean_object* v___x_2110_; uint8_t v_isShared_2111_; uint8_t v_isSharedCheck_2129_; 
v_presentation_2105_ = lean_ctor_get(v_x_1440_, 0);
lean_inc(v_presentation_2105_);
lean_dec_ref(v_x_1440_);
v___x_2106_ = l___private_Std_Time_Notation_0__Std_Time_convertNumber(v_presentation_2105_, v_a_1441_, v_a_1442_);
v_a_2107_ = lean_ctor_get(v___x_2106_, 0);
v_a_2108_ = lean_ctor_get(v___x_2106_, 1);
v_isSharedCheck_2129_ = !lean_is_exclusive(v___x_2106_);
if (v_isSharedCheck_2129_ == 0)
{
v___x_2110_ = v___x_2106_;
v_isShared_2111_ = v_isSharedCheck_2129_;
goto v_resetjp_2109_;
}
else
{
lean_inc(v_a_2108_);
lean_inc(v_a_2107_);
lean_dec(v___x_2106_);
v___x_2110_ = lean_box(0);
v_isShared_2111_ = v_isSharedCheck_2129_;
goto v_resetjp_2109_;
}
v_resetjp_2109_:
{
lean_object* v_quotContext_2112_; lean_object* v_currMacroScope_2113_; lean_object* v_ref_2114_; uint8_t v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2127_; 
v_quotContext_2112_ = lean_ctor_get(v_a_1441_, 1);
v_currMacroScope_2113_ = lean_ctor_get(v_a_1441_, 2);
v_ref_2114_ = lean_ctor_get(v_a_1441_, 5);
v___x_2115_ = 0;
v___x_2116_ = l_Lean_SourceInfo_fromRef(v_ref_2114_, v___x_2115_);
v___x_2117_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2118_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__173, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__173_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__173);
v___x_2119_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__175));
lean_inc(v_currMacroScope_2113_);
lean_inc(v_quotContext_2112_);
v___x_2120_ = l_Lean_addMacroScope(v_quotContext_2112_, v___x_2119_, v_currMacroScope_2113_);
v___x_2121_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__179));
lean_inc_n(v___x_2116_, 2);
v___x_2122_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2122_, 0, v___x_2116_);
lean_ctor_set(v___x_2122_, 1, v___x_2118_);
lean_ctor_set(v___x_2122_, 2, v___x_2120_);
lean_ctor_set(v___x_2122_, 3, v___x_2121_);
v___x_2123_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2124_ = l_Lean_Syntax_node1(v___x_2116_, v___x_2123_, v_a_2107_);
v___x_2125_ = l_Lean_Syntax_node2(v___x_2116_, v___x_2117_, v___x_2122_, v___x_2124_);
if (v_isShared_2111_ == 0)
{
lean_ctor_set(v___x_2110_, 0, v___x_2125_);
v___x_2127_ = v___x_2110_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v___x_2125_);
lean_ctor_set(v_reuseFailAlloc_2128_, 1, v_a_2108_);
v___x_2127_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
return v___x_2127_;
}
}
}
case 18:
{
lean_object* v_presentation_2130_; lean_object* v___x_2131_; lean_object* v_a_2132_; lean_object* v_a_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2154_; 
v_presentation_2130_ = lean_ctor_get(v_x_1440_, 0);
lean_inc(v_presentation_2130_);
lean_dec_ref(v_x_1440_);
v___x_2131_ = l___private_Std_Time_Notation_0__Std_Time_convertNumber(v_presentation_2130_, v_a_1441_, v_a_1442_);
v_a_2132_ = lean_ctor_get(v___x_2131_, 0);
v_a_2133_ = lean_ctor_get(v___x_2131_, 1);
v_isSharedCheck_2154_ = !lean_is_exclusive(v___x_2131_);
if (v_isSharedCheck_2154_ == 0)
{
v___x_2135_ = v___x_2131_;
v_isShared_2136_ = v_isSharedCheck_2154_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_a_2133_);
lean_inc(v_a_2132_);
lean_dec(v___x_2131_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2154_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v_quotContext_2137_; lean_object* v_currMacroScope_2138_; lean_object* v_ref_2139_; uint8_t v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2152_; 
v_quotContext_2137_ = lean_ctor_get(v_a_1441_, 1);
v_currMacroScope_2138_ = lean_ctor_get(v_a_1441_, 2);
v_ref_2139_ = lean_ctor_get(v_a_1441_, 5);
v___x_2140_ = 0;
v___x_2141_ = l_Lean_SourceInfo_fromRef(v_ref_2139_, v___x_2140_);
v___x_2142_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2143_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__181, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__181_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__181);
v___x_2144_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__183));
lean_inc(v_currMacroScope_2138_);
lean_inc(v_quotContext_2137_);
v___x_2145_ = l_Lean_addMacroScope(v_quotContext_2137_, v___x_2144_, v_currMacroScope_2138_);
v___x_2146_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__187));
lean_inc_n(v___x_2141_, 2);
v___x_2147_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2147_, 0, v___x_2141_);
lean_ctor_set(v___x_2147_, 1, v___x_2143_);
lean_ctor_set(v___x_2147_, 2, v___x_2145_);
lean_ctor_set(v___x_2147_, 3, v___x_2146_);
v___x_2148_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2149_ = l_Lean_Syntax_node1(v___x_2141_, v___x_2148_, v_a_2132_);
v___x_2150_ = l_Lean_Syntax_node2(v___x_2141_, v___x_2142_, v___x_2147_, v___x_2149_);
if (v_isShared_2136_ == 0)
{
lean_ctor_set(v___x_2135_, 0, v___x_2150_);
v___x_2152_ = v___x_2135_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v___x_2150_);
lean_ctor_set(v_reuseFailAlloc_2153_, 1, v_a_2133_);
v___x_2152_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
return v___x_2152_;
}
}
}
case 19:
{
lean_object* v_presentation_2155_; lean_object* v___x_2156_; lean_object* v_a_2157_; lean_object* v_a_2158_; lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2179_; 
v_presentation_2155_ = lean_ctor_get(v_x_1440_, 0);
lean_inc(v_presentation_2155_);
lean_dec_ref(v_x_1440_);
v___x_2156_ = l___private_Std_Time_Notation_0__Std_Time_convertFraction(v_presentation_2155_, v_a_1441_, v_a_1442_);
v_a_2157_ = lean_ctor_get(v___x_2156_, 0);
v_a_2158_ = lean_ctor_get(v___x_2156_, 1);
v_isSharedCheck_2179_ = !lean_is_exclusive(v___x_2156_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2160_ = v___x_2156_;
v_isShared_2161_ = v_isSharedCheck_2179_;
goto v_resetjp_2159_;
}
else
{
lean_inc(v_a_2158_);
lean_inc(v_a_2157_);
lean_dec(v___x_2156_);
v___x_2160_ = lean_box(0);
v_isShared_2161_ = v_isSharedCheck_2179_;
goto v_resetjp_2159_;
}
v_resetjp_2159_:
{
lean_object* v_quotContext_2162_; lean_object* v_currMacroScope_2163_; lean_object* v_ref_2164_; uint8_t v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2177_; 
v_quotContext_2162_ = lean_ctor_get(v_a_1441_, 1);
v_currMacroScope_2163_ = lean_ctor_get(v_a_1441_, 2);
v_ref_2164_ = lean_ctor_get(v_a_1441_, 5);
v___x_2165_ = 0;
v___x_2166_ = l_Lean_SourceInfo_fromRef(v_ref_2164_, v___x_2165_);
v___x_2167_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2168_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__189, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__189_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__189);
v___x_2169_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__191));
lean_inc(v_currMacroScope_2163_);
lean_inc(v_quotContext_2162_);
v___x_2170_ = l_Lean_addMacroScope(v_quotContext_2162_, v___x_2169_, v_currMacroScope_2163_);
v___x_2171_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__195));
lean_inc_n(v___x_2166_, 2);
v___x_2172_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2172_, 0, v___x_2166_);
lean_ctor_set(v___x_2172_, 1, v___x_2168_);
lean_ctor_set(v___x_2172_, 2, v___x_2170_);
lean_ctor_set(v___x_2172_, 3, v___x_2171_);
v___x_2173_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2174_ = l_Lean_Syntax_node1(v___x_2166_, v___x_2173_, v_a_2157_);
v___x_2175_ = l_Lean_Syntax_node2(v___x_2166_, v___x_2167_, v___x_2172_, v___x_2174_);
if (v_isShared_2161_ == 0)
{
lean_ctor_set(v___x_2160_, 0, v___x_2175_);
v___x_2177_ = v___x_2160_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v___x_2175_);
lean_ctor_set(v_reuseFailAlloc_2178_, 1, v_a_2158_);
v___x_2177_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
return v___x_2177_;
}
}
}
case 20:
{
lean_object* v_presentation_2180_; lean_object* v___x_2181_; lean_object* v_a_2182_; lean_object* v_a_2183_; lean_object* v___x_2185_; uint8_t v_isShared_2186_; uint8_t v_isSharedCheck_2204_; 
v_presentation_2180_ = lean_ctor_get(v_x_1440_, 0);
lean_inc(v_presentation_2180_);
lean_dec_ref(v_x_1440_);
v___x_2181_ = l___private_Std_Time_Notation_0__Std_Time_convertNumber(v_presentation_2180_, v_a_1441_, v_a_1442_);
v_a_2182_ = lean_ctor_get(v___x_2181_, 0);
v_a_2183_ = lean_ctor_get(v___x_2181_, 1);
v_isSharedCheck_2204_ = !lean_is_exclusive(v___x_2181_);
if (v_isSharedCheck_2204_ == 0)
{
v___x_2185_ = v___x_2181_;
v_isShared_2186_ = v_isSharedCheck_2204_;
goto v_resetjp_2184_;
}
else
{
lean_inc(v_a_2183_);
lean_inc(v_a_2182_);
lean_dec(v___x_2181_);
v___x_2185_ = lean_box(0);
v_isShared_2186_ = v_isSharedCheck_2204_;
goto v_resetjp_2184_;
}
v_resetjp_2184_:
{
lean_object* v_quotContext_2187_; lean_object* v_currMacroScope_2188_; lean_object* v_ref_2189_; uint8_t v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2202_; 
v_quotContext_2187_ = lean_ctor_get(v_a_1441_, 1);
v_currMacroScope_2188_ = lean_ctor_get(v_a_1441_, 2);
v_ref_2189_ = lean_ctor_get(v_a_1441_, 5);
v___x_2190_ = 0;
v___x_2191_ = l_Lean_SourceInfo_fromRef(v_ref_2189_, v___x_2190_);
v___x_2192_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2193_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__197, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__197_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__197);
v___x_2194_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__199));
lean_inc(v_currMacroScope_2188_);
lean_inc(v_quotContext_2187_);
v___x_2195_ = l_Lean_addMacroScope(v_quotContext_2187_, v___x_2194_, v_currMacroScope_2188_);
v___x_2196_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__203));
lean_inc_n(v___x_2191_, 2);
v___x_2197_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2197_, 0, v___x_2191_);
lean_ctor_set(v___x_2197_, 1, v___x_2193_);
lean_ctor_set(v___x_2197_, 2, v___x_2195_);
lean_ctor_set(v___x_2197_, 3, v___x_2196_);
v___x_2198_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2199_ = l_Lean_Syntax_node1(v___x_2191_, v___x_2198_, v_a_2182_);
v___x_2200_ = l_Lean_Syntax_node2(v___x_2191_, v___x_2192_, v___x_2197_, v___x_2199_);
if (v_isShared_2186_ == 0)
{
lean_ctor_set(v___x_2185_, 0, v___x_2200_);
v___x_2202_ = v___x_2185_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v___x_2200_);
lean_ctor_set(v_reuseFailAlloc_2203_, 1, v_a_2183_);
v___x_2202_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2201_;
}
v_reusejp_2201_:
{
return v___x_2202_;
}
}
}
case 21:
{
lean_object* v_presentation_2205_; lean_object* v___x_2206_; lean_object* v_a_2207_; lean_object* v_a_2208_; lean_object* v___x_2210_; uint8_t v_isShared_2211_; uint8_t v_isSharedCheck_2229_; 
v_presentation_2205_ = lean_ctor_get(v_x_1440_, 0);
lean_inc(v_presentation_2205_);
lean_dec_ref(v_x_1440_);
v___x_2206_ = l___private_Std_Time_Notation_0__Std_Time_convertNumber(v_presentation_2205_, v_a_1441_, v_a_1442_);
v_a_2207_ = lean_ctor_get(v___x_2206_, 0);
v_a_2208_ = lean_ctor_get(v___x_2206_, 1);
v_isSharedCheck_2229_ = !lean_is_exclusive(v___x_2206_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_2210_ = v___x_2206_;
v_isShared_2211_ = v_isSharedCheck_2229_;
goto v_resetjp_2209_;
}
else
{
lean_inc(v_a_2208_);
lean_inc(v_a_2207_);
lean_dec(v___x_2206_);
v___x_2210_ = lean_box(0);
v_isShared_2211_ = v_isSharedCheck_2229_;
goto v_resetjp_2209_;
}
v_resetjp_2209_:
{
lean_object* v_quotContext_2212_; lean_object* v_currMacroScope_2213_; lean_object* v_ref_2214_; uint8_t v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2227_; 
v_quotContext_2212_ = lean_ctor_get(v_a_1441_, 1);
v_currMacroScope_2213_ = lean_ctor_get(v_a_1441_, 2);
v_ref_2214_ = lean_ctor_get(v_a_1441_, 5);
v___x_2215_ = 0;
v___x_2216_ = l_Lean_SourceInfo_fromRef(v_ref_2214_, v___x_2215_);
v___x_2217_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2218_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__205, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__205_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__205);
v___x_2219_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__207));
lean_inc(v_currMacroScope_2213_);
lean_inc(v_quotContext_2212_);
v___x_2220_ = l_Lean_addMacroScope(v_quotContext_2212_, v___x_2219_, v_currMacroScope_2213_);
v___x_2221_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__211));
lean_inc_n(v___x_2216_, 2);
v___x_2222_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2222_, 0, v___x_2216_);
lean_ctor_set(v___x_2222_, 1, v___x_2218_);
lean_ctor_set(v___x_2222_, 2, v___x_2220_);
lean_ctor_set(v___x_2222_, 3, v___x_2221_);
v___x_2223_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2224_ = l_Lean_Syntax_node1(v___x_2216_, v___x_2223_, v_a_2207_);
v___x_2225_ = l_Lean_Syntax_node2(v___x_2216_, v___x_2217_, v___x_2222_, v___x_2224_);
if (v_isShared_2211_ == 0)
{
lean_ctor_set(v___x_2210_, 0, v___x_2225_);
v___x_2227_ = v___x_2210_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v___x_2225_);
lean_ctor_set(v_reuseFailAlloc_2228_, 1, v_a_2208_);
v___x_2227_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
return v___x_2227_;
}
}
}
case 22:
{
lean_object* v_presentation_2230_; lean_object* v___x_2231_; lean_object* v_a_2232_; lean_object* v_a_2233_; lean_object* v___x_2235_; uint8_t v_isShared_2236_; uint8_t v_isSharedCheck_2254_; 
v_presentation_2230_ = lean_ctor_get(v_x_1440_, 0);
lean_inc(v_presentation_2230_);
lean_dec_ref(v_x_1440_);
v___x_2231_ = l___private_Std_Time_Notation_0__Std_Time_convertNumber(v_presentation_2230_, v_a_1441_, v_a_1442_);
v_a_2232_ = lean_ctor_get(v___x_2231_, 0);
v_a_2233_ = lean_ctor_get(v___x_2231_, 1);
v_isSharedCheck_2254_ = !lean_is_exclusive(v___x_2231_);
if (v_isSharedCheck_2254_ == 0)
{
v___x_2235_ = v___x_2231_;
v_isShared_2236_ = v_isSharedCheck_2254_;
goto v_resetjp_2234_;
}
else
{
lean_inc(v_a_2233_);
lean_inc(v_a_2232_);
lean_dec(v___x_2231_);
v___x_2235_ = lean_box(0);
v_isShared_2236_ = v_isSharedCheck_2254_;
goto v_resetjp_2234_;
}
v_resetjp_2234_:
{
lean_object* v_quotContext_2237_; lean_object* v_currMacroScope_2238_; lean_object* v_ref_2239_; uint8_t v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2252_; 
v_quotContext_2237_ = lean_ctor_get(v_a_1441_, 1);
v_currMacroScope_2238_ = lean_ctor_get(v_a_1441_, 2);
v_ref_2239_ = lean_ctor_get(v_a_1441_, 5);
v___x_2240_ = 0;
v___x_2241_ = l_Lean_SourceInfo_fromRef(v_ref_2239_, v___x_2240_);
v___x_2242_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2243_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__213, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__213_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__213);
v___x_2244_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__215));
lean_inc(v_currMacroScope_2238_);
lean_inc(v_quotContext_2237_);
v___x_2245_ = l_Lean_addMacroScope(v_quotContext_2237_, v___x_2244_, v_currMacroScope_2238_);
v___x_2246_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__219));
lean_inc_n(v___x_2241_, 2);
v___x_2247_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2247_, 0, v___x_2241_);
lean_ctor_set(v___x_2247_, 1, v___x_2243_);
lean_ctor_set(v___x_2247_, 2, v___x_2245_);
lean_ctor_set(v___x_2247_, 3, v___x_2246_);
v___x_2248_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2249_ = l_Lean_Syntax_node1(v___x_2241_, v___x_2248_, v_a_2232_);
v___x_2250_ = l_Lean_Syntax_node2(v___x_2241_, v___x_2242_, v___x_2247_, v___x_2249_);
if (v_isShared_2236_ == 0)
{
lean_ctor_set(v___x_2235_, 0, v___x_2250_);
v___x_2252_ = v___x_2235_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v___x_2250_);
lean_ctor_set(v_reuseFailAlloc_2253_, 1, v_a_2233_);
v___x_2252_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2251_;
}
v_reusejp_2251_:
{
return v___x_2252_;
}
}
}
case 23:
{
lean_object* v_quotContext_2255_; lean_object* v_currMacroScope_2256_; lean_object* v_ref_2257_; uint8_t v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; 
v_quotContext_2255_ = lean_ctor_get(v_a_1441_, 1);
v_currMacroScope_2256_ = lean_ctor_get(v_a_1441_, 2);
v_ref_2257_ = lean_ctor_get(v_a_1441_, 5);
v___x_2258_ = 0;
v___x_2259_ = l_Lean_SourceInfo_fromRef(v_ref_2257_, v___x_2258_);
v___x_2260_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__221, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__221_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__221);
v___x_2261_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__223));
lean_inc(v_currMacroScope_2256_);
lean_inc(v_quotContext_2255_);
v___x_2262_ = l_Lean_addMacroScope(v_quotContext_2255_, v___x_2261_, v_currMacroScope_2256_);
v___x_2263_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__227));
v___x_2264_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2264_, 0, v___x_2259_);
lean_ctor_set(v___x_2264_, 1, v___x_2260_);
lean_ctor_set(v___x_2264_, 2, v___x_2262_);
lean_ctor_set(v___x_2264_, 3, v___x_2263_);
v___x_2265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2265_, 0, v___x_2264_);
lean_ctor_set(v___x_2265_, 1, v_a_1442_);
return v___x_2265_;
}
case 24:
{
uint8_t v_presentation_2266_; lean_object* v___x_2267_; lean_object* v_a_2268_; lean_object* v_a_2269_; lean_object* v___x_2271_; uint8_t v_isShared_2272_; uint8_t v_isSharedCheck_2290_; 
v_presentation_2266_ = lean_ctor_get_uint8(v_x_1440_, 0);
lean_dec_ref(v_x_1440_);
v___x_2267_ = l___private_Std_Time_Notation_0__Std_Time_convertZoneName(v_presentation_2266_, v_a_1441_, v_a_1442_);
v_a_2268_ = lean_ctor_get(v___x_2267_, 0);
v_a_2269_ = lean_ctor_get(v___x_2267_, 1);
v_isSharedCheck_2290_ = !lean_is_exclusive(v___x_2267_);
if (v_isSharedCheck_2290_ == 0)
{
v___x_2271_ = v___x_2267_;
v_isShared_2272_ = v_isSharedCheck_2290_;
goto v_resetjp_2270_;
}
else
{
lean_inc(v_a_2269_);
lean_inc(v_a_2268_);
lean_dec(v___x_2267_);
v___x_2271_ = lean_box(0);
v_isShared_2272_ = v_isSharedCheck_2290_;
goto v_resetjp_2270_;
}
v_resetjp_2270_:
{
lean_object* v_quotContext_2273_; lean_object* v_currMacroScope_2274_; lean_object* v_ref_2275_; uint8_t v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2288_; 
v_quotContext_2273_ = lean_ctor_get(v_a_1441_, 1);
v_currMacroScope_2274_ = lean_ctor_get(v_a_1441_, 2);
v_ref_2275_ = lean_ctor_get(v_a_1441_, 5);
v___x_2276_ = 0;
v___x_2277_ = l_Lean_SourceInfo_fromRef(v_ref_2275_, v___x_2276_);
v___x_2278_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2279_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__229, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__229_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__229);
v___x_2280_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__231));
lean_inc(v_currMacroScope_2274_);
lean_inc(v_quotContext_2273_);
v___x_2281_ = l_Lean_addMacroScope(v_quotContext_2273_, v___x_2280_, v_currMacroScope_2274_);
v___x_2282_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__235));
lean_inc_n(v___x_2277_, 2);
v___x_2283_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2283_, 0, v___x_2277_);
lean_ctor_set(v___x_2283_, 1, v___x_2279_);
lean_ctor_set(v___x_2283_, 2, v___x_2281_);
lean_ctor_set(v___x_2283_, 3, v___x_2282_);
v___x_2284_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2285_ = l_Lean_Syntax_node1(v___x_2277_, v___x_2284_, v_a_2268_);
v___x_2286_ = l_Lean_Syntax_node2(v___x_2277_, v___x_2278_, v___x_2283_, v___x_2285_);
if (v_isShared_2272_ == 0)
{
lean_ctor_set(v___x_2271_, 0, v___x_2286_);
v___x_2288_ = v___x_2271_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2289_; 
v_reuseFailAlloc_2289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2289_, 0, v___x_2286_);
lean_ctor_set(v_reuseFailAlloc_2289_, 1, v_a_2269_);
v___x_2288_ = v_reuseFailAlloc_2289_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
return v___x_2288_;
}
}
}
case 25:
{
uint8_t v_presentation_2291_; lean_object* v___x_2292_; lean_object* v_a_2293_; lean_object* v_a_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2315_; 
v_presentation_2291_ = lean_ctor_get_uint8(v_x_1440_, 0);
lean_dec_ref(v_x_1440_);
v___x_2292_ = l___private_Std_Time_Notation_0__Std_Time_convertOffsetO(v_presentation_2291_, v_a_1441_, v_a_1442_);
v_a_2293_ = lean_ctor_get(v___x_2292_, 0);
v_a_2294_ = lean_ctor_get(v___x_2292_, 1);
v_isSharedCheck_2315_ = !lean_is_exclusive(v___x_2292_);
if (v_isSharedCheck_2315_ == 0)
{
v___x_2296_ = v___x_2292_;
v_isShared_2297_ = v_isSharedCheck_2315_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_a_2294_);
lean_inc(v_a_2293_);
lean_dec(v___x_2292_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2315_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v_quotContext_2298_; lean_object* v_currMacroScope_2299_; lean_object* v_ref_2300_; uint8_t v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2313_; 
v_quotContext_2298_ = lean_ctor_get(v_a_1441_, 1);
v_currMacroScope_2299_ = lean_ctor_get(v_a_1441_, 2);
v_ref_2300_ = lean_ctor_get(v_a_1441_, 5);
v___x_2301_ = 0;
v___x_2302_ = l_Lean_SourceInfo_fromRef(v_ref_2300_, v___x_2301_);
v___x_2303_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2304_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__237, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__237_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__237);
v___x_2305_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__239));
lean_inc(v_currMacroScope_2299_);
lean_inc(v_quotContext_2298_);
v___x_2306_ = l_Lean_addMacroScope(v_quotContext_2298_, v___x_2305_, v_currMacroScope_2299_);
v___x_2307_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__243));
lean_inc_n(v___x_2302_, 2);
v___x_2308_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2308_, 0, v___x_2302_);
lean_ctor_set(v___x_2308_, 1, v___x_2304_);
lean_ctor_set(v___x_2308_, 2, v___x_2306_);
lean_ctor_set(v___x_2308_, 3, v___x_2307_);
v___x_2309_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2310_ = l_Lean_Syntax_node1(v___x_2302_, v___x_2309_, v_a_2293_);
v___x_2311_ = l_Lean_Syntax_node2(v___x_2302_, v___x_2303_, v___x_2308_, v___x_2310_);
if (v_isShared_2297_ == 0)
{
lean_ctor_set(v___x_2296_, 0, v___x_2311_);
v___x_2313_ = v___x_2296_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v___x_2311_);
lean_ctor_set(v_reuseFailAlloc_2314_, 1, v_a_2294_);
v___x_2313_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
return v___x_2313_;
}
}
}
case 26:
{
uint8_t v_presentation_2316_; lean_object* v___x_2317_; lean_object* v_a_2318_; lean_object* v_a_2319_; lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2340_; 
v_presentation_2316_ = lean_ctor_get_uint8(v_x_1440_, 0);
lean_dec_ref(v_x_1440_);
v___x_2317_ = l___private_Std_Time_Notation_0__Std_Time_convertOffsetX(v_presentation_2316_, v_a_1441_, v_a_1442_);
v_a_2318_ = lean_ctor_get(v___x_2317_, 0);
v_a_2319_ = lean_ctor_get(v___x_2317_, 1);
v_isSharedCheck_2340_ = !lean_is_exclusive(v___x_2317_);
if (v_isSharedCheck_2340_ == 0)
{
v___x_2321_ = v___x_2317_;
v_isShared_2322_ = v_isSharedCheck_2340_;
goto v_resetjp_2320_;
}
else
{
lean_inc(v_a_2319_);
lean_inc(v_a_2318_);
lean_dec(v___x_2317_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2340_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
lean_object* v_quotContext_2323_; lean_object* v_currMacroScope_2324_; lean_object* v_ref_2325_; uint8_t v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2338_; 
v_quotContext_2323_ = lean_ctor_get(v_a_1441_, 1);
v_currMacroScope_2324_ = lean_ctor_get(v_a_1441_, 2);
v_ref_2325_ = lean_ctor_get(v_a_1441_, 5);
v___x_2326_ = 0;
v___x_2327_ = l_Lean_SourceInfo_fromRef(v_ref_2325_, v___x_2326_);
v___x_2328_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2329_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__245, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__245_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__245);
v___x_2330_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__247));
lean_inc(v_currMacroScope_2324_);
lean_inc(v_quotContext_2323_);
v___x_2331_ = l_Lean_addMacroScope(v_quotContext_2323_, v___x_2330_, v_currMacroScope_2324_);
v___x_2332_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__251));
lean_inc_n(v___x_2327_, 2);
v___x_2333_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2333_, 0, v___x_2327_);
lean_ctor_set(v___x_2333_, 1, v___x_2329_);
lean_ctor_set(v___x_2333_, 2, v___x_2331_);
lean_ctor_set(v___x_2333_, 3, v___x_2332_);
v___x_2334_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2335_ = l_Lean_Syntax_node1(v___x_2327_, v___x_2334_, v_a_2318_);
v___x_2336_ = l_Lean_Syntax_node2(v___x_2327_, v___x_2328_, v___x_2333_, v___x_2335_);
if (v_isShared_2322_ == 0)
{
lean_ctor_set(v___x_2321_, 0, v___x_2336_);
v___x_2338_ = v___x_2321_;
goto v_reusejp_2337_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v___x_2336_);
lean_ctor_set(v_reuseFailAlloc_2339_, 1, v_a_2319_);
v___x_2338_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2337_;
}
v_reusejp_2337_:
{
return v___x_2338_;
}
}
}
case 27:
{
uint8_t v_presentation_2341_; lean_object* v___x_2342_; lean_object* v_a_2343_; lean_object* v_a_2344_; lean_object* v___x_2346_; uint8_t v_isShared_2347_; uint8_t v_isSharedCheck_2365_; 
v_presentation_2341_ = lean_ctor_get_uint8(v_x_1440_, 0);
lean_dec_ref(v_x_1440_);
v___x_2342_ = l___private_Std_Time_Notation_0__Std_Time_convertOffsetX(v_presentation_2341_, v_a_1441_, v_a_1442_);
v_a_2343_ = lean_ctor_get(v___x_2342_, 0);
v_a_2344_ = lean_ctor_get(v___x_2342_, 1);
v_isSharedCheck_2365_ = !lean_is_exclusive(v___x_2342_);
if (v_isSharedCheck_2365_ == 0)
{
v___x_2346_ = v___x_2342_;
v_isShared_2347_ = v_isSharedCheck_2365_;
goto v_resetjp_2345_;
}
else
{
lean_inc(v_a_2344_);
lean_inc(v_a_2343_);
lean_dec(v___x_2342_);
v___x_2346_ = lean_box(0);
v_isShared_2347_ = v_isSharedCheck_2365_;
goto v_resetjp_2345_;
}
v_resetjp_2345_:
{
lean_object* v_quotContext_2348_; lean_object* v_currMacroScope_2349_; lean_object* v_ref_2350_; uint8_t v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2363_; 
v_quotContext_2348_ = lean_ctor_get(v_a_1441_, 1);
v_currMacroScope_2349_ = lean_ctor_get(v_a_1441_, 2);
v_ref_2350_ = lean_ctor_get(v_a_1441_, 5);
v___x_2351_ = 0;
v___x_2352_ = l_Lean_SourceInfo_fromRef(v_ref_2350_, v___x_2351_);
v___x_2353_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2354_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__253, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__253_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__253);
v___x_2355_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__255));
lean_inc(v_currMacroScope_2349_);
lean_inc(v_quotContext_2348_);
v___x_2356_ = l_Lean_addMacroScope(v_quotContext_2348_, v___x_2355_, v_currMacroScope_2349_);
v___x_2357_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__259));
lean_inc_n(v___x_2352_, 2);
v___x_2358_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2358_, 0, v___x_2352_);
lean_ctor_set(v___x_2358_, 1, v___x_2354_);
lean_ctor_set(v___x_2358_, 2, v___x_2356_);
lean_ctor_set(v___x_2358_, 3, v___x_2357_);
v___x_2359_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2360_ = l_Lean_Syntax_node1(v___x_2352_, v___x_2359_, v_a_2343_);
v___x_2361_ = l_Lean_Syntax_node2(v___x_2352_, v___x_2353_, v___x_2358_, v___x_2360_);
if (v_isShared_2347_ == 0)
{
lean_ctor_set(v___x_2346_, 0, v___x_2361_);
v___x_2363_ = v___x_2346_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v___x_2361_);
lean_ctor_set(v_reuseFailAlloc_2364_, 1, v_a_2344_);
v___x_2363_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
return v___x_2363_;
}
}
}
default: 
{
uint8_t v_presentation_2366_; lean_object* v___x_2367_; lean_object* v_a_2368_; lean_object* v_a_2369_; lean_object* v___x_2371_; uint8_t v_isShared_2372_; uint8_t v_isSharedCheck_2390_; 
v_presentation_2366_ = lean_ctor_get_uint8(v_x_1440_, 0);
lean_dec_ref(v_x_1440_);
v___x_2367_ = l___private_Std_Time_Notation_0__Std_Time_convertOffsetZ(v_presentation_2366_, v_a_1441_, v_a_1442_);
v_a_2368_ = lean_ctor_get(v___x_2367_, 0);
v_a_2369_ = lean_ctor_get(v___x_2367_, 1);
v_isSharedCheck_2390_ = !lean_is_exclusive(v___x_2367_);
if (v_isSharedCheck_2390_ == 0)
{
v___x_2371_ = v___x_2367_;
v_isShared_2372_ = v_isSharedCheck_2390_;
goto v_resetjp_2370_;
}
else
{
lean_inc(v_a_2369_);
lean_inc(v_a_2368_);
lean_dec(v___x_2367_);
v___x_2371_ = lean_box(0);
v_isShared_2372_ = v_isSharedCheck_2390_;
goto v_resetjp_2370_;
}
v_resetjp_2370_:
{
lean_object* v_quotContext_2373_; lean_object* v_currMacroScope_2374_; lean_object* v_ref_2375_; uint8_t v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2388_; 
v_quotContext_2373_ = lean_ctor_get(v_a_1441_, 1);
v_currMacroScope_2374_ = lean_ctor_get(v_a_1441_, 2);
v_ref_2375_ = lean_ctor_get(v_a_1441_, 5);
v___x_2376_ = 0;
v___x_2377_ = l_Lean_SourceInfo_fromRef(v_ref_2375_, v___x_2376_);
v___x_2378_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2379_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__261, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__261_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__261);
v___x_2380_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__263));
lean_inc(v_currMacroScope_2374_);
lean_inc(v_quotContext_2373_);
v___x_2381_ = l_Lean_addMacroScope(v_quotContext_2373_, v___x_2380_, v_currMacroScope_2374_);
v___x_2382_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__267));
lean_inc_n(v___x_2377_, 2);
v___x_2383_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2383_, 0, v___x_2377_);
lean_ctor_set(v___x_2383_, 1, v___x_2379_);
lean_ctor_set(v___x_2383_, 2, v___x_2381_);
lean_ctor_set(v___x_2383_, 3, v___x_2382_);
v___x_2384_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2385_ = l_Lean_Syntax_node1(v___x_2377_, v___x_2384_, v_a_2368_);
v___x_2386_ = l_Lean_Syntax_node2(v___x_2377_, v___x_2378_, v___x_2383_, v___x_2385_);
if (v_isShared_2372_ == 0)
{
lean_ctor_set(v___x_2371_, 0, v___x_2386_);
v___x_2388_ = v___x_2371_;
goto v_reusejp_2387_;
}
else
{
lean_object* v_reuseFailAlloc_2389_; 
v_reuseFailAlloc_2389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2389_, 0, v___x_2386_);
lean_ctor_set(v_reuseFailAlloc_2389_, 1, v_a_2369_);
v___x_2388_ = v_reuseFailAlloc_2389_;
goto v_reusejp_2387_;
}
v_reusejp_2387_:
{
return v___x_2388_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertModifier___boxed(lean_object* v_x_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_){
_start:
{
lean_object* v_res_2394_; 
v_res_2394_ = l___private_Std_Time_Notation_0__Std_Time_convertModifier(v_x_2391_, v_a_2392_, v_a_2393_);
lean_dec_ref(v_a_2392_);
return v_res_2394_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertFormatPart___closed__1(void){
_start:
{
lean_object* v___x_2396_; lean_object* v___x_2397_; 
v___x_2396_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertFormatPart___closed__0));
v___x_2397_ = l_String_toRawSubstring_x27(v___x_2396_);
return v___x_2397_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertFormatPart___closed__4(void){
_start:
{
lean_object* v___x_2401_; lean_object* v___x_2402_; 
v___x_2401_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertFormatPart___closed__3));
v___x_2402_ = l_String_toRawSubstring_x27(v___x_2401_);
return v___x_2402_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertFormatPart(lean_object* v_x_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_){
_start:
{
if (lean_obj_tag(v_x_2405_) == 0)
{
lean_object* v_val_2408_; lean_object* v_quotContext_2409_; lean_object* v_currMacroScope_2410_; lean_object* v_ref_2411_; uint8_t v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; 
v_val_2408_ = lean_ctor_get(v_x_2405_, 0);
lean_inc_ref(v_val_2408_);
lean_dec_ref(v_x_2405_);
v_quotContext_2409_ = lean_ctor_get(v_a_2406_, 1);
v_currMacroScope_2410_ = lean_ctor_get(v_a_2406_, 2);
v_ref_2411_ = lean_ctor_get(v_a_2406_, 5);
v___x_2412_ = 0;
v___x_2413_ = l_Lean_SourceInfo_fromRef(v_ref_2411_, v___x_2412_);
v___x_2414_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2415_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__67));
v___x_2416_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__68));
lean_inc_n(v___x_2413_, 4);
v___x_2417_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2417_, 0, v___x_2413_);
lean_ctor_set(v___x_2417_, 1, v___x_2416_);
v___x_2418_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertFormatPart___closed__1, &l___private_Std_Time_Notation_0__Std_Time_convertFormatPart___closed__1_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertFormatPart___closed__1);
v___x_2419_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertFormatPart___closed__2));
lean_inc(v_currMacroScope_2410_);
lean_inc(v_quotContext_2409_);
v___x_2420_ = l_Lean_addMacroScope(v_quotContext_2409_, v___x_2419_, v_currMacroScope_2410_);
v___x_2421_ = lean_box(0);
v___x_2422_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2422_, 0, v___x_2413_);
lean_ctor_set(v___x_2422_, 1, v___x_2418_);
lean_ctor_set(v___x_2422_, 2, v___x_2420_);
lean_ctor_set(v___x_2422_, 3, v___x_2421_);
v___x_2423_ = l_Lean_Syntax_node2(v___x_2413_, v___x_2415_, v___x_2417_, v___x_2422_);
v___x_2424_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2425_ = lean_box(2);
v___x_2426_ = l_Lean_Syntax_mkStrLit(v_val_2408_, v___x_2425_);
v___x_2427_ = l_Lean_Syntax_node1(v___x_2413_, v___x_2424_, v___x_2426_);
v___x_2428_ = l_Lean_Syntax_node2(v___x_2413_, v___x_2414_, v___x_2423_, v___x_2427_);
v___x_2429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2429_, 0, v___x_2428_);
lean_ctor_set(v___x_2429_, 1, v_a_2407_);
return v___x_2429_;
}
else
{
lean_object* v_modifier_2430_; lean_object* v___x_2431_; lean_object* v_a_2432_; lean_object* v_a_2433_; lean_object* v___x_2435_; uint8_t v_isShared_2436_; uint8_t v_isSharedCheck_2458_; 
v_modifier_2430_ = lean_ctor_get(v_x_2405_, 0);
lean_inc(v_modifier_2430_);
lean_dec_ref(v_x_2405_);
v___x_2431_ = l___private_Std_Time_Notation_0__Std_Time_convertModifier(v_modifier_2430_, v_a_2406_, v_a_2407_);
v_a_2432_ = lean_ctor_get(v___x_2431_, 0);
v_a_2433_ = lean_ctor_get(v___x_2431_, 1);
v_isSharedCheck_2458_ = !lean_is_exclusive(v___x_2431_);
if (v_isSharedCheck_2458_ == 0)
{
v___x_2435_ = v___x_2431_;
v_isShared_2436_ = v_isSharedCheck_2458_;
goto v_resetjp_2434_;
}
else
{
lean_inc(v_a_2433_);
lean_inc(v_a_2432_);
lean_dec(v___x_2431_);
v___x_2435_ = lean_box(0);
v_isShared_2436_ = v_isSharedCheck_2458_;
goto v_resetjp_2434_;
}
v_resetjp_2434_:
{
lean_object* v_quotContext_2437_; lean_object* v_currMacroScope_2438_; lean_object* v_ref_2439_; uint8_t v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2456_; 
v_quotContext_2437_ = lean_ctor_get(v_a_2406_, 1);
v_currMacroScope_2438_ = lean_ctor_get(v_a_2406_, 2);
v_ref_2439_ = lean_ctor_get(v_a_2406_, 5);
v___x_2440_ = 0;
v___x_2441_ = l_Lean_SourceInfo_fromRef(v_ref_2439_, v___x_2440_);
v___x_2442_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2443_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__67));
v___x_2444_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__68));
lean_inc_n(v___x_2441_, 4);
v___x_2445_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2445_, 0, v___x_2441_);
lean_ctor_set(v___x_2445_, 1, v___x_2444_);
v___x_2446_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertFormatPart___closed__4, &l___private_Std_Time_Notation_0__Std_Time_convertFormatPart___closed__4_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertFormatPart___closed__4);
v___x_2447_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertFormatPart___closed__5));
lean_inc(v_currMacroScope_2438_);
lean_inc(v_quotContext_2437_);
v___x_2448_ = l_Lean_addMacroScope(v_quotContext_2437_, v___x_2447_, v_currMacroScope_2438_);
v___x_2449_ = lean_box(0);
v___x_2450_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2450_, 0, v___x_2441_);
lean_ctor_set(v___x_2450_, 1, v___x_2446_);
lean_ctor_set(v___x_2450_, 2, v___x_2448_);
lean_ctor_set(v___x_2450_, 3, v___x_2449_);
v___x_2451_ = l_Lean_Syntax_node2(v___x_2441_, v___x_2443_, v___x_2445_, v___x_2450_);
v___x_2452_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2453_ = l_Lean_Syntax_node1(v___x_2441_, v___x_2452_, v_a_2432_);
v___x_2454_ = l_Lean_Syntax_node2(v___x_2441_, v___x_2442_, v___x_2451_, v___x_2453_);
if (v_isShared_2436_ == 0)
{
lean_ctor_set(v___x_2435_, 0, v___x_2454_);
v___x_2456_ = v___x_2435_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v___x_2454_);
lean_ctor_set(v_reuseFailAlloc_2457_, 1, v_a_2433_);
v___x_2456_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
return v___x_2456_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertFormatPart___boxed(lean_object* v_x_2459_, lean_object* v_a_2460_, lean_object* v_a_2461_){
_start:
{
lean_object* v_res_2462_; 
v_res_2462_ = l___private_Std_Time_Notation_0__Std_Time_convertFormatPart(v_x_2459_, v_a_2460_, v_a_2461_);
lean_dec_ref(v_a_2460_);
return v_res_2462_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxNat(lean_object* v_n_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_){
_start:
{
lean_object* v_ref_2469_; uint8_t v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; 
v_ref_2469_ = lean_ctor_get(v_a_2467_, 5);
v___x_2470_ = 0;
v___x_2471_ = l_Lean_SourceInfo_fromRef(v_ref_2469_, v___x_2470_);
v___x_2472_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxNat___closed__1));
v___x_2473_ = l_Nat_reprFast(v_n_2466_);
lean_inc(v___x_2471_);
v___x_2474_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2474_, 0, v___x_2471_);
lean_ctor_set(v___x_2474_, 1, v___x_2473_);
v___x_2475_ = l_Lean_Syntax_node1(v___x_2471_, v___x_2472_, v___x_2474_);
v___x_2476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2476_, 0, v___x_2475_);
lean_ctor_set(v___x_2476_, 1, v_a_2468_);
return v___x_2476_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxNat___boxed(lean_object* v_n_2477_, lean_object* v_a_2478_, lean_object* v_a_2479_){
_start:
{
lean_object* v_res_2480_; 
v_res_2480_ = l___private_Std_Time_Notation_0__Std_Time_syntaxNat(v_n_2477_, v_a_2478_, v_a_2479_);
lean_dec_ref(v_a_2478_);
return v_res_2480_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxString(lean_object* v_n_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_){
_start:
{
lean_object* v_ref_2487_; uint8_t v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; 
v_ref_2487_ = lean_ctor_get(v_a_2485_, 5);
v___x_2488_ = 0;
v___x_2489_ = l_Lean_SourceInfo_fromRef(v_ref_2487_, v___x_2488_);
v___x_2490_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxString___closed__1));
lean_inc(v___x_2489_);
v___x_2491_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2491_, 0, v___x_2489_);
lean_ctor_set(v___x_2491_, 1, v_n_2484_);
v___x_2492_ = l_Lean_Syntax_node1(v___x_2489_, v___x_2490_, v___x_2491_);
v___x_2493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2493_, 0, v___x_2492_);
lean_ctor_set(v___x_2493_, 1, v_a_2486_);
return v___x_2493_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxString___boxed(lean_object* v_n_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_){
_start:
{
lean_object* v_res_2497_; 
v_res_2497_ = l___private_Std_Time_Notation_0__Std_Time_syntaxString(v_n_2494_, v_a_2495_, v_a_2496_);
lean_dec_ref(v_a_2495_);
return v_res_2497_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__0(void){
_start:
{
lean_object* v_natZero_2498_; lean_object* v_intZero_2499_; 
v_natZero_2498_ = lean_unsigned_to_nat(0u);
v_intZero_2499_ = lean_nat_to_int(v_natZero_2498_);
return v_intZero_2499_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__2(void){
_start:
{
lean_object* v___x_2501_; lean_object* v___x_2502_; 
v___x_2501_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__1));
v___x_2502_ = l_String_toRawSubstring_x27(v___x_2501_);
return v___x_2502_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__11(void){
_start:
{
lean_object* v___x_2520_; lean_object* v___x_2521_; 
v___x_2520_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__10));
v___x_2521_ = l_String_toRawSubstring_x27(v___x_2520_);
return v___x_2521_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxInt(lean_object* v_n_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_){
_start:
{
lean_object* v_intZero_2540_; uint8_t v_isNeg_2541_; 
v_intZero_2540_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__0, &l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__0_once, _init_l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__0);
v_isNeg_2541_ = lean_int_dec_lt(v_n_2537_, v_intZero_2540_);
if (v_isNeg_2541_ == 0)
{
lean_object* v_quotContext_2542_; lean_object* v_currMacroScope_2543_; lean_object* v_ref_2544_; lean_object* v_a_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; 
v_quotContext_2542_ = lean_ctor_get(v_a_2538_, 1);
v_currMacroScope_2543_ = lean_ctor_get(v_a_2538_, 2);
v_ref_2544_ = lean_ctor_get(v_a_2538_, 5);
v_a_2545_ = lean_nat_abs(v_n_2537_);
v___x_2546_ = l_Lean_SourceInfo_fromRef(v_ref_2544_, v_isNeg_2541_);
v___x_2547_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2548_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__2, &l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__2_once, _init_l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__2);
v___x_2549_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__5));
lean_inc(v_currMacroScope_2543_);
lean_inc(v_quotContext_2542_);
v___x_2550_ = l_Lean_addMacroScope(v_quotContext_2542_, v___x_2549_, v_currMacroScope_2543_);
v___x_2551_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__9));
lean_inc_n(v___x_2546_, 2);
v___x_2552_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2552_, 0, v___x_2546_);
lean_ctor_set(v___x_2552_, 1, v___x_2548_);
lean_ctor_set(v___x_2552_, 2, v___x_2550_);
lean_ctor_set(v___x_2552_, 3, v___x_2551_);
v___x_2553_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2554_ = l_Nat_reprFast(v_a_2545_);
v___x_2555_ = lean_box(2);
v___x_2556_ = l_Lean_Syntax_mkNumLit(v___x_2554_, v___x_2555_);
v___x_2557_ = l_Lean_Syntax_node1(v___x_2546_, v___x_2553_, v___x_2556_);
v___x_2558_ = l_Lean_Syntax_node2(v___x_2546_, v___x_2547_, v___x_2552_, v___x_2557_);
v___x_2559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2559_, 0, v___x_2558_);
lean_ctor_set(v___x_2559_, 1, v_a_2539_);
return v___x_2559_;
}
else
{
lean_object* v_quotContext_2560_; lean_object* v_currMacroScope_2561_; lean_object* v_ref_2562_; lean_object* v_abs_2563_; lean_object* v_one_2564_; lean_object* v_a_2565_; uint8_t v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; 
v_quotContext_2560_ = lean_ctor_get(v_a_2538_, 1);
v_currMacroScope_2561_ = lean_ctor_get(v_a_2538_, 2);
v_ref_2562_ = lean_ctor_get(v_a_2538_, 5);
v_abs_2563_ = lean_nat_abs(v_n_2537_);
v_one_2564_ = lean_unsigned_to_nat(1u);
v_a_2565_ = lean_nat_sub(v_abs_2563_, v_one_2564_);
lean_dec(v_abs_2563_);
v___x_2566_ = 0;
v___x_2567_ = l_Lean_SourceInfo_fromRef(v_ref_2562_, v___x_2566_);
v___x_2568_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2569_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__11, &l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__11_once, _init_l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__11);
v___x_2570_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__13));
lean_inc(v_currMacroScope_2561_);
lean_inc(v_quotContext_2560_);
v___x_2571_ = l_Lean_addMacroScope(v_quotContext_2560_, v___x_2570_, v_currMacroScope_2561_);
v___x_2572_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxInt___closed__17));
lean_inc_n(v___x_2567_, 2);
v___x_2573_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2573_, 0, v___x_2567_);
lean_ctor_set(v___x_2573_, 1, v___x_2569_);
lean_ctor_set(v___x_2573_, 2, v___x_2571_);
lean_ctor_set(v___x_2573_, 3, v___x_2572_);
v___x_2574_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2575_ = l_Nat_reprFast(v_a_2565_);
v___x_2576_ = lean_box(2);
v___x_2577_ = l_Lean_Syntax_mkNumLit(v___x_2575_, v___x_2576_);
v___x_2578_ = l_Lean_Syntax_node1(v___x_2567_, v___x_2574_, v___x_2577_);
v___x_2579_ = l_Lean_Syntax_node2(v___x_2567_, v___x_2568_, v___x_2573_, v___x_2578_);
v___x_2580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2580_, 0, v___x_2579_);
lean_ctor_set(v___x_2580_, 1, v_a_2539_);
return v___x_2580_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxInt___boxed(lean_object* v_n_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_){
_start:
{
lean_object* v_res_2584_; 
v_res_2584_ = l___private_Std_Time_Notation_0__Std_Time_syntaxInt(v_n_2581_, v_a_2582_, v_a_2583_);
lean_dec_ref(v_a_2582_);
lean_dec(v_n_2581_);
return v_res_2584_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__1(void){
_start:
{
lean_object* v___x_2586_; lean_object* v___x_2587_; 
v___x_2586_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__0));
v___x_2587_ = l_String_toRawSubstring_x27(v___x_2586_);
return v___x_2587_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__21(void){
_start:
{
lean_object* v___x_2637_; 
v___x_2637_ = l_Array_mkArray0(lean_box(0));
return v___x_2637_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxBounded(lean_object* v_n_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_){
_start:
{
lean_object* v___x_2641_; lean_object* v_a_2642_; lean_object* v_a_2643_; lean_object* v___x_2645_; uint8_t v_isShared_2646_; uint8_t v_isSharedCheck_2696_; 
v___x_2641_ = l___private_Std_Time_Notation_0__Std_Time_syntaxInt(v_n_2638_, v_a_2639_, v_a_2640_);
v_a_2642_ = lean_ctor_get(v___x_2641_, 0);
v_a_2643_ = lean_ctor_get(v___x_2641_, 1);
v_isSharedCheck_2696_ = !lean_is_exclusive(v___x_2641_);
if (v_isSharedCheck_2696_ == 0)
{
v___x_2645_ = v___x_2641_;
v_isShared_2646_ = v_isSharedCheck_2696_;
goto v_resetjp_2644_;
}
else
{
lean_inc(v_a_2643_);
lean_inc(v_a_2642_);
lean_dec(v___x_2641_);
v___x_2645_ = lean_box(0);
v_isShared_2646_ = v_isSharedCheck_2696_;
goto v_resetjp_2644_;
}
v_resetjp_2644_:
{
lean_object* v_quotContext_2647_; lean_object* v_currMacroScope_2648_; lean_object* v_ref_2649_; uint8_t v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2694_; 
v_quotContext_2647_ = lean_ctor_get(v_a_2639_, 1);
v_currMacroScope_2648_ = lean_ctor_get(v_a_2639_, 2);
v_ref_2649_ = lean_ctor_get(v_a_2639_, 5);
v___x_2650_ = 0;
v___x_2651_ = l_Lean_SourceInfo_fromRef(v_ref_2649_, v___x_2650_);
v___x_2652_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2653_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__1, &l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__1_once, _init_l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__1);
v___x_2654_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__6));
lean_inc_n(v_currMacroScope_2648_, 2);
lean_inc_n(v_quotContext_2647_, 2);
v___x_2655_ = l_Lean_addMacroScope(v_quotContext_2647_, v___x_2654_, v_currMacroScope_2648_);
v___x_2656_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__8));
lean_inc_n(v___x_2651_, 17);
v___x_2657_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2657_, 0, v___x_2651_);
lean_ctor_set(v___x_2657_, 1, v___x_2653_);
lean_ctor_set(v___x_2657_, 2, v___x_2655_);
lean_ctor_set(v___x_2657_, 3, v___x_2656_);
v___x_2658_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2659_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__42));
v___x_2660_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__44));
v___x_2661_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__45));
v___x_2662_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2662_, 0, v___x_2651_);
lean_ctor_set(v___x_2662_, 1, v___x_2661_);
v___x_2663_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__47));
v___x_2664_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49);
v___x_2665_ = lean_box(0);
v___x_2666_ = l_Lean_addMacroScope(v_quotContext_2647_, v___x_2665_, v_currMacroScope_2648_);
v___x_2667_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__65));
v___x_2668_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2668_, 0, v___x_2651_);
lean_ctor_set(v___x_2668_, 1, v___x_2664_);
lean_ctor_set(v___x_2668_, 2, v___x_2666_);
lean_ctor_set(v___x_2668_, 3, v___x_2667_);
v___x_2669_ = l_Lean_Syntax_node1(v___x_2651_, v___x_2663_, v___x_2668_);
v___x_2670_ = l_Lean_Syntax_node2(v___x_2651_, v___x_2660_, v___x_2662_, v___x_2669_);
v___x_2671_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__10));
v___x_2672_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__11));
v___x_2673_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2673_, 0, v___x_2651_);
lean_ctor_set(v___x_2673_, 1, v___x_2672_);
v___x_2674_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__14));
v___x_2675_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__16));
v___x_2676_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__17));
v___x_2677_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__18));
v___x_2678_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2678_, 0, v___x_2651_);
lean_ctor_set(v___x_2678_, 1, v___x_2676_);
v___x_2679_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__20));
v___x_2680_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__21, &l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__21_once, _init_l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___closed__21);
v___x_2681_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2681_, 0, v___x_2651_);
lean_ctor_set(v___x_2681_, 1, v___x_2658_);
lean_ctor_set(v___x_2681_, 2, v___x_2680_);
v___x_2682_ = l_Lean_Syntax_node1(v___x_2651_, v___x_2679_, v___x_2681_);
v___x_2683_ = l_Lean_Syntax_node2(v___x_2651_, v___x_2677_, v___x_2678_, v___x_2682_);
v___x_2684_ = l_Lean_Syntax_node1(v___x_2651_, v___x_2658_, v___x_2683_);
v___x_2685_ = l_Lean_Syntax_node1(v___x_2651_, v___x_2675_, v___x_2684_);
v___x_2686_ = l_Lean_Syntax_node1(v___x_2651_, v___x_2674_, v___x_2685_);
v___x_2687_ = l_Lean_Syntax_node2(v___x_2651_, v___x_2671_, v___x_2673_, v___x_2686_);
v___x_2688_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__72));
v___x_2689_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2689_, 0, v___x_2651_);
lean_ctor_set(v___x_2689_, 1, v___x_2688_);
v___x_2690_ = l_Lean_Syntax_node3(v___x_2651_, v___x_2659_, v___x_2670_, v___x_2687_, v___x_2689_);
v___x_2691_ = l_Lean_Syntax_node2(v___x_2651_, v___x_2658_, v_a_2642_, v___x_2690_);
v___x_2692_ = l_Lean_Syntax_node2(v___x_2651_, v___x_2652_, v___x_2657_, v___x_2691_);
if (v_isShared_2646_ == 0)
{
lean_ctor_set(v___x_2645_, 0, v___x_2692_);
v___x_2694_ = v___x_2645_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v___x_2692_);
lean_ctor_set(v_reuseFailAlloc_2695_, 1, v_a_2643_);
v___x_2694_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2693_;
}
v_reusejp_2693_:
{
return v___x_2694_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxBounded___boxed(lean_object* v_n_2697_, lean_object* v_a_2698_, lean_object* v_a_2699_){
_start:
{
lean_object* v_res_2700_; 
v_res_2700_ = l___private_Std_Time_Notation_0__Std_Time_syntaxBounded(v_n_2697_, v_a_2698_, v_a_2699_);
lean_dec_ref(v_a_2698_);
lean_dec(v_n_2697_);
return v_res_2700_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_syntaxVal___closed__1(void){
_start:
{
lean_object* v___x_2702_; lean_object* v___x_2703_; 
v___x_2702_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxVal___closed__0));
v___x_2703_ = l_String_toRawSubstring_x27(v___x_2702_);
return v___x_2703_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxVal(lean_object* v_n_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_){
_start:
{
lean_object* v___x_2726_; lean_object* v_a_2727_; lean_object* v_a_2728_; lean_object* v___x_2730_; uint8_t v_isShared_2731_; uint8_t v_isSharedCheck_2749_; 
v___x_2726_ = l___private_Std_Time_Notation_0__Std_Time_syntaxInt(v_n_2723_, v_a_2724_, v_a_2725_);
v_a_2727_ = lean_ctor_get(v___x_2726_, 0);
v_a_2728_ = lean_ctor_get(v___x_2726_, 1);
v_isSharedCheck_2749_ = !lean_is_exclusive(v___x_2726_);
if (v_isSharedCheck_2749_ == 0)
{
v___x_2730_ = v___x_2726_;
v_isShared_2731_ = v_isSharedCheck_2749_;
goto v_resetjp_2729_;
}
else
{
lean_inc(v_a_2728_);
lean_inc(v_a_2727_);
lean_dec(v___x_2726_);
v___x_2730_ = lean_box(0);
v_isShared_2731_ = v_isSharedCheck_2749_;
goto v_resetjp_2729_;
}
v_resetjp_2729_:
{
lean_object* v_quotContext_2732_; lean_object* v_currMacroScope_2733_; lean_object* v_ref_2734_; uint8_t v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2747_; 
v_quotContext_2732_ = lean_ctor_get(v_a_2724_, 1);
v_currMacroScope_2733_ = lean_ctor_get(v_a_2724_, 2);
v_ref_2734_ = lean_ctor_get(v_a_2724_, 5);
v___x_2735_ = 0;
v___x_2736_ = l_Lean_SourceInfo_fromRef(v_ref_2734_, v___x_2735_);
v___x_2737_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2738_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_syntaxVal___closed__1, &l___private_Std_Time_Notation_0__Std_Time_syntaxVal___closed__1_once, _init_l___private_Std_Time_Notation_0__Std_Time_syntaxVal___closed__1);
v___x_2739_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxVal___closed__4));
lean_inc(v_currMacroScope_2733_);
lean_inc(v_quotContext_2732_);
v___x_2740_ = l_Lean_addMacroScope(v_quotContext_2732_, v___x_2739_, v_currMacroScope_2733_);
v___x_2741_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxVal___closed__8));
lean_inc_n(v___x_2736_, 2);
v___x_2742_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2742_, 0, v___x_2736_);
lean_ctor_set(v___x_2742_, 1, v___x_2738_);
lean_ctor_set(v___x_2742_, 2, v___x_2740_);
lean_ctor_set(v___x_2742_, 3, v___x_2741_);
v___x_2743_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2744_ = l_Lean_Syntax_node1(v___x_2736_, v___x_2743_, v_a_2727_);
v___x_2745_ = l_Lean_Syntax_node2(v___x_2736_, v___x_2737_, v___x_2742_, v___x_2744_);
if (v_isShared_2731_ == 0)
{
lean_ctor_set(v___x_2730_, 0, v___x_2745_);
v___x_2747_ = v___x_2730_;
goto v_reusejp_2746_;
}
else
{
lean_object* v_reuseFailAlloc_2748_; 
v_reuseFailAlloc_2748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2748_, 0, v___x_2745_);
lean_ctor_set(v_reuseFailAlloc_2748_, 1, v_a_2728_);
v___x_2747_ = v_reuseFailAlloc_2748_;
goto v_reusejp_2746_;
}
v_reusejp_2746_:
{
return v___x_2747_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_syntaxVal___boxed(lean_object* v_n_2750_, lean_object* v_a_2751_, lean_object* v_a_2752_){
_start:
{
lean_object* v_res_2753_; 
v_res_2753_ = l___private_Std_Time_Notation_0__Std_Time_syntaxVal(v_n_2750_, v_a_2751_, v_a_2752_);
lean_dec_ref(v_a_2751_);
lean_dec(v_n_2750_);
return v_res_2753_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertOffset___closed__1(void){
_start:
{
lean_object* v___x_2755_; lean_object* v___x_2756_; 
v___x_2755_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffset___closed__0));
v___x_2756_ = l_String_toRawSubstring_x27(v___x_2755_);
return v___x_2756_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffset(lean_object* v_offset_2777_, lean_object* v_a_2778_, lean_object* v_a_2779_){
_start:
{
lean_object* v___x_2780_; lean_object* v_a_2781_; lean_object* v_a_2782_; lean_object* v___x_2784_; uint8_t v_isShared_2785_; uint8_t v_isSharedCheck_2803_; 
v___x_2780_ = l___private_Std_Time_Notation_0__Std_Time_syntaxVal(v_offset_2777_, v_a_2778_, v_a_2779_);
v_a_2781_ = lean_ctor_get(v___x_2780_, 0);
v_a_2782_ = lean_ctor_get(v___x_2780_, 1);
v_isSharedCheck_2803_ = !lean_is_exclusive(v___x_2780_);
if (v_isSharedCheck_2803_ == 0)
{
v___x_2784_ = v___x_2780_;
v_isShared_2785_ = v_isSharedCheck_2803_;
goto v_resetjp_2783_;
}
else
{
lean_inc(v_a_2782_);
lean_inc(v_a_2781_);
lean_dec(v___x_2780_);
v___x_2784_ = lean_box(0);
v_isShared_2785_ = v_isSharedCheck_2803_;
goto v_resetjp_2783_;
}
v_resetjp_2783_:
{
lean_object* v_quotContext_2786_; lean_object* v_currMacroScope_2787_; lean_object* v_ref_2788_; uint8_t v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2801_; 
v_quotContext_2786_ = lean_ctor_get(v_a_2778_, 1);
v_currMacroScope_2787_ = lean_ctor_get(v_a_2778_, 2);
v_ref_2788_ = lean_ctor_get(v_a_2778_, 5);
v___x_2789_ = 0;
v___x_2790_ = l_Lean_SourceInfo_fromRef(v_ref_2788_, v___x_2789_);
v___x_2791_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2792_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertOffset___closed__1, &l___private_Std_Time_Notation_0__Std_Time_convertOffset___closed__1_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertOffset___closed__1);
v___x_2793_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffset___closed__5));
lean_inc(v_currMacroScope_2787_);
lean_inc(v_quotContext_2786_);
v___x_2794_ = l_Lean_addMacroScope(v_quotContext_2786_, v___x_2793_, v_currMacroScope_2787_);
v___x_2795_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertOffset___closed__9));
lean_inc_n(v___x_2790_, 2);
v___x_2796_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2796_, 0, v___x_2790_);
lean_ctor_set(v___x_2796_, 1, v___x_2792_);
lean_ctor_set(v___x_2796_, 2, v___x_2794_);
lean_ctor_set(v___x_2796_, 3, v___x_2795_);
v___x_2797_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2798_ = l_Lean_Syntax_node1(v___x_2790_, v___x_2797_, v_a_2781_);
v___x_2799_ = l_Lean_Syntax_node2(v___x_2790_, v___x_2791_, v___x_2796_, v___x_2798_);
if (v_isShared_2785_ == 0)
{
lean_ctor_set(v___x_2784_, 0, v___x_2799_);
v___x_2801_ = v___x_2784_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v___x_2799_);
lean_ctor_set(v_reuseFailAlloc_2802_, 1, v_a_2782_);
v___x_2801_ = v_reuseFailAlloc_2802_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
return v___x_2801_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertOffset___boxed(lean_object* v_offset_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_){
_start:
{
lean_object* v_res_2807_; 
v_res_2807_ = l___private_Std_Time_Notation_0__Std_Time_convertOffset(v_offset_2804_, v_a_2805_, v_a_2806_);
lean_dec_ref(v_a_2805_);
lean_dec(v_offset_2804_);
return v_res_2807_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__1(void){
_start:
{
lean_object* v___x_2809_; lean_object* v___x_2810_; 
v___x_2809_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__0));
v___x_2810_ = l_String_toRawSubstring_x27(v___x_2809_);
return v___x_2810_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__8(void){
_start:
{
lean_object* v___x_2828_; lean_object* v___x_2829_; 
v___x_2828_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__7));
v___x_2829_ = l_String_toRawSubstring_x27(v___x_2828_);
return v___x_2829_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertTimezone(lean_object* v_tz_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_){
_start:
{
lean_object* v_offset_2845_; lean_object* v_name_2846_; lean_object* v_abbreviation_2847_; lean_object* v___x_2848_; lean_object* v_a_2849_; lean_object* v_a_2850_; lean_object* v___x_2852_; uint8_t v_isShared_2853_; uint8_t v_isSharedCheck_2879_; 
v_offset_2845_ = lean_ctor_get(v_tz_2842_, 0);
lean_inc(v_offset_2845_);
v_name_2846_ = lean_ctor_get(v_tz_2842_, 1);
lean_inc_ref(v_name_2846_);
v_abbreviation_2847_ = lean_ctor_get(v_tz_2842_, 2);
lean_inc_ref(v_abbreviation_2847_);
lean_dec_ref(v_tz_2842_);
v___x_2848_ = l___private_Std_Time_Notation_0__Std_Time_convertOffset(v_offset_2845_, v_a_2843_, v_a_2844_);
lean_dec(v_offset_2845_);
v_a_2849_ = lean_ctor_get(v___x_2848_, 0);
v_a_2850_ = lean_ctor_get(v___x_2848_, 1);
v_isSharedCheck_2879_ = !lean_is_exclusive(v___x_2848_);
if (v_isSharedCheck_2879_ == 0)
{
v___x_2852_ = v___x_2848_;
v_isShared_2853_ = v_isSharedCheck_2879_;
goto v_resetjp_2851_;
}
else
{
lean_inc(v_a_2850_);
lean_inc(v_a_2849_);
lean_dec(v___x_2848_);
v___x_2852_ = lean_box(0);
v_isShared_2853_ = v_isSharedCheck_2879_;
goto v_resetjp_2851_;
}
v_resetjp_2851_:
{
lean_object* v_quotContext_2854_; lean_object* v_currMacroScope_2855_; lean_object* v_ref_2856_; uint8_t v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2877_; 
v_quotContext_2854_ = lean_ctor_get(v_a_2843_, 1);
v_currMacroScope_2855_ = lean_ctor_get(v_a_2843_, 2);
v_ref_2856_ = lean_ctor_get(v_a_2843_, 5);
v___x_2857_ = 0;
v___x_2858_ = l_Lean_SourceInfo_fromRef(v_ref_2856_, v___x_2857_);
v___x_2859_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2860_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__1, &l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__1_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__1);
v___x_2861_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__2));
lean_inc_n(v_currMacroScope_2855_, 2);
lean_inc_n(v_quotContext_2854_, 2);
v___x_2862_ = l_Lean_addMacroScope(v_quotContext_2854_, v___x_2861_, v_currMacroScope_2855_);
v___x_2863_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__6));
lean_inc_n(v___x_2858_, 3);
v___x_2864_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2864_, 0, v___x_2858_);
lean_ctor_set(v___x_2864_, 1, v___x_2860_);
lean_ctor_set(v___x_2864_, 2, v___x_2862_);
lean_ctor_set(v___x_2864_, 3, v___x_2863_);
v___x_2865_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2866_ = lean_box(2);
v___x_2867_ = l_Lean_Syntax_mkStrLit(v_name_2846_, v___x_2866_);
v___x_2868_ = l_Lean_Syntax_mkStrLit(v_abbreviation_2847_, v___x_2866_);
v___x_2869_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__8, &l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__8_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__8);
v___x_2870_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__9));
v___x_2871_ = l_Lean_addMacroScope(v_quotContext_2854_, v___x_2870_, v_currMacroScope_2855_);
v___x_2872_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertTimezone___closed__13));
v___x_2873_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2873_, 0, v___x_2858_);
lean_ctor_set(v___x_2873_, 1, v___x_2869_);
lean_ctor_set(v___x_2873_, 2, v___x_2871_);
lean_ctor_set(v___x_2873_, 3, v___x_2872_);
v___x_2874_ = l_Lean_Syntax_node4(v___x_2858_, v___x_2865_, v_a_2849_, v___x_2867_, v___x_2868_, v___x_2873_);
v___x_2875_ = l_Lean_Syntax_node2(v___x_2858_, v___x_2859_, v___x_2864_, v___x_2874_);
if (v_isShared_2853_ == 0)
{
lean_ctor_set(v___x_2852_, 0, v___x_2875_);
v___x_2877_ = v___x_2852_;
goto v_reusejp_2876_;
}
else
{
lean_object* v_reuseFailAlloc_2878_; 
v_reuseFailAlloc_2878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2878_, 0, v___x_2875_);
lean_ctor_set(v_reuseFailAlloc_2878_, 1, v_a_2850_);
v___x_2877_ = v_reuseFailAlloc_2878_;
goto v_reusejp_2876_;
}
v_reusejp_2876_:
{
return v___x_2877_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertTimezone___boxed(lean_object* v_tz_2880_, lean_object* v_a_2881_, lean_object* v_a_2882_){
_start:
{
lean_object* v_res_2883_; 
v_res_2883_ = l___private_Std_Time_Notation_0__Std_Time_convertTimezone(v_tz_2880_, v_a_2881_, v_a_2882_);
lean_dec_ref(v_a_2881_);
return v_res_2883_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertPlainDate___closed__1(void){
_start:
{
lean_object* v___x_2885_; lean_object* v___x_2886_; 
v___x_2885_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertPlainDate___closed__0));
v___x_2886_ = l_String_toRawSubstring_x27(v___x_2885_);
return v___x_2886_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertPlainDate(lean_object* v_d_2900_, lean_object* v_a_2901_, lean_object* v_a_2902_){
_start:
{
lean_object* v_year_2903_; lean_object* v_month_2904_; lean_object* v_day_2905_; lean_object* v___x_2906_; lean_object* v_a_2907_; lean_object* v_a_2908_; lean_object* v___x_2909_; lean_object* v_a_2910_; lean_object* v_a_2911_; lean_object* v___x_2912_; lean_object* v_a_2913_; lean_object* v_a_2914_; lean_object* v___x_2916_; uint8_t v_isShared_2917_; uint8_t v_isSharedCheck_2935_; 
v_year_2903_ = lean_ctor_get(v_d_2900_, 0);
v_month_2904_ = lean_ctor_get(v_d_2900_, 1);
v_day_2905_ = lean_ctor_get(v_d_2900_, 2);
v___x_2906_ = l___private_Std_Time_Notation_0__Std_Time_syntaxInt(v_year_2903_, v_a_2901_, v_a_2902_);
v_a_2907_ = lean_ctor_get(v___x_2906_, 0);
lean_inc(v_a_2907_);
v_a_2908_ = lean_ctor_get(v___x_2906_, 1);
lean_inc(v_a_2908_);
lean_dec_ref(v___x_2906_);
v___x_2909_ = l___private_Std_Time_Notation_0__Std_Time_syntaxBounded(v_month_2904_, v_a_2901_, v_a_2908_);
v_a_2910_ = lean_ctor_get(v___x_2909_, 0);
lean_inc(v_a_2910_);
v_a_2911_ = lean_ctor_get(v___x_2909_, 1);
lean_inc(v_a_2911_);
lean_dec_ref(v___x_2909_);
v___x_2912_ = l___private_Std_Time_Notation_0__Std_Time_syntaxBounded(v_day_2905_, v_a_2901_, v_a_2911_);
v_a_2913_ = lean_ctor_get(v___x_2912_, 0);
v_a_2914_ = lean_ctor_get(v___x_2912_, 1);
v_isSharedCheck_2935_ = !lean_is_exclusive(v___x_2912_);
if (v_isSharedCheck_2935_ == 0)
{
v___x_2916_ = v___x_2912_;
v_isShared_2917_ = v_isSharedCheck_2935_;
goto v_resetjp_2915_;
}
else
{
lean_inc(v_a_2914_);
lean_inc(v_a_2913_);
lean_dec(v___x_2912_);
v___x_2916_ = lean_box(0);
v_isShared_2917_ = v_isSharedCheck_2935_;
goto v_resetjp_2915_;
}
v_resetjp_2915_:
{
lean_object* v_quotContext_2918_; lean_object* v_currMacroScope_2919_; lean_object* v_ref_2920_; uint8_t v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2933_; 
v_quotContext_2918_ = lean_ctor_get(v_a_2901_, 1);
v_currMacroScope_2919_ = lean_ctor_get(v_a_2901_, 2);
v_ref_2920_ = lean_ctor_get(v_a_2901_, 5);
v___x_2921_ = 0;
v___x_2922_ = l_Lean_SourceInfo_fromRef(v_ref_2920_, v___x_2921_);
v___x_2923_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2924_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertPlainDate___closed__1, &l___private_Std_Time_Notation_0__Std_Time_convertPlainDate___closed__1_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertPlainDate___closed__1);
v___x_2925_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertPlainDate___closed__4));
lean_inc(v_currMacroScope_2919_);
lean_inc(v_quotContext_2918_);
v___x_2926_ = l_Lean_addMacroScope(v_quotContext_2918_, v___x_2925_, v_currMacroScope_2919_);
v___x_2927_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertPlainDate___closed__6));
lean_inc_n(v___x_2922_, 2);
v___x_2928_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2928_, 0, v___x_2922_);
lean_ctor_set(v___x_2928_, 1, v___x_2924_);
lean_ctor_set(v___x_2928_, 2, v___x_2926_);
lean_ctor_set(v___x_2928_, 3, v___x_2927_);
v___x_2929_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_2930_ = l_Lean_Syntax_node3(v___x_2922_, v___x_2929_, v_a_2907_, v_a_2910_, v_a_2913_);
v___x_2931_ = l_Lean_Syntax_node2(v___x_2922_, v___x_2923_, v___x_2928_, v___x_2930_);
if (v_isShared_2917_ == 0)
{
lean_ctor_set(v___x_2916_, 0, v___x_2931_);
v___x_2933_ = v___x_2916_;
goto v_reusejp_2932_;
}
else
{
lean_object* v_reuseFailAlloc_2934_; 
v_reuseFailAlloc_2934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2934_, 0, v___x_2931_);
lean_ctor_set(v_reuseFailAlloc_2934_, 1, v_a_2914_);
v___x_2933_ = v_reuseFailAlloc_2934_;
goto v_reusejp_2932_;
}
v_reusejp_2932_:
{
return v___x_2933_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertPlainDate___boxed(lean_object* v_d_2936_, lean_object* v_a_2937_, lean_object* v_a_2938_){
_start:
{
lean_object* v_res_2939_; 
v_res_2939_ = l___private_Std_Time_Notation_0__Std_Time_convertPlainDate(v_d_2936_, v_a_2937_, v_a_2938_);
lean_dec_ref(v_a_2937_);
lean_dec_ref(v_d_2936_);
return v_res_2939_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertPlainTime___closed__1(void){
_start:
{
lean_object* v___x_2941_; lean_object* v___x_2942_; 
v___x_2941_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertPlainTime___closed__0));
v___x_2942_ = l_String_toRawSubstring_x27(v___x_2941_);
return v___x_2942_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertPlainTime(lean_object* v_d_2960_, lean_object* v_a_2961_, lean_object* v_a_2962_){
_start:
{
lean_object* v_hour_2963_; lean_object* v_minute_2964_; lean_object* v_second_2965_; lean_object* v_nanosecond_2966_; lean_object* v___x_2968_; uint8_t v_isShared_2969_; uint8_t v_isSharedCheck_3005_; 
v_hour_2963_ = lean_ctor_get(v_d_2960_, 0);
v_minute_2964_ = lean_ctor_get(v_d_2960_, 1);
v_second_2965_ = lean_ctor_get(v_d_2960_, 2);
v_nanosecond_2966_ = lean_ctor_get(v_d_2960_, 3);
v_isSharedCheck_3005_ = !lean_is_exclusive(v_d_2960_);
if (v_isSharedCheck_3005_ == 0)
{
v___x_2968_ = v_d_2960_;
v_isShared_2969_ = v_isSharedCheck_3005_;
goto v_resetjp_2967_;
}
else
{
lean_inc(v_nanosecond_2966_);
lean_inc(v_second_2965_);
lean_inc(v_minute_2964_);
lean_inc(v_hour_2963_);
lean_dec(v_d_2960_);
v___x_2968_ = lean_box(0);
v_isShared_2969_ = v_isSharedCheck_3005_;
goto v_resetjp_2967_;
}
v_resetjp_2967_:
{
lean_object* v___x_2970_; lean_object* v_a_2971_; lean_object* v_a_2972_; lean_object* v___x_2973_; lean_object* v_a_2974_; lean_object* v_a_2975_; lean_object* v___x_2976_; lean_object* v_a_2977_; lean_object* v_a_2978_; lean_object* v___x_2979_; lean_object* v_a_2980_; lean_object* v_a_2981_; lean_object* v___x_2983_; uint8_t v_isShared_2984_; uint8_t v_isSharedCheck_3004_; 
v___x_2970_ = l___private_Std_Time_Notation_0__Std_Time_syntaxBounded(v_hour_2963_, v_a_2961_, v_a_2962_);
lean_dec(v_hour_2963_);
v_a_2971_ = lean_ctor_get(v___x_2970_, 0);
lean_inc(v_a_2971_);
v_a_2972_ = lean_ctor_get(v___x_2970_, 1);
lean_inc(v_a_2972_);
lean_dec_ref(v___x_2970_);
v___x_2973_ = l___private_Std_Time_Notation_0__Std_Time_syntaxBounded(v_minute_2964_, v_a_2961_, v_a_2972_);
lean_dec(v_minute_2964_);
v_a_2974_ = lean_ctor_get(v___x_2973_, 0);
lean_inc(v_a_2974_);
v_a_2975_ = lean_ctor_get(v___x_2973_, 1);
lean_inc(v_a_2975_);
lean_dec_ref(v___x_2973_);
v___x_2976_ = l___private_Std_Time_Notation_0__Std_Time_syntaxBounded(v_second_2965_, v_a_2961_, v_a_2975_);
lean_dec(v_second_2965_);
v_a_2977_ = lean_ctor_get(v___x_2976_, 0);
lean_inc(v_a_2977_);
v_a_2978_ = lean_ctor_get(v___x_2976_, 1);
lean_inc(v_a_2978_);
lean_dec_ref(v___x_2976_);
v___x_2979_ = l___private_Std_Time_Notation_0__Std_Time_syntaxBounded(v_nanosecond_2966_, v_a_2961_, v_a_2978_);
lean_dec(v_nanosecond_2966_);
v_a_2980_ = lean_ctor_get(v___x_2979_, 0);
v_a_2981_ = lean_ctor_get(v___x_2979_, 1);
v_isSharedCheck_3004_ = !lean_is_exclusive(v___x_2979_);
if (v_isSharedCheck_3004_ == 0)
{
v___x_2983_ = v___x_2979_;
v_isShared_2984_ = v_isSharedCheck_3004_;
goto v_resetjp_2982_;
}
else
{
lean_inc(v_a_2981_);
lean_inc(v_a_2980_);
lean_dec(v___x_2979_);
v___x_2983_ = lean_box(0);
v_isShared_2984_ = v_isSharedCheck_3004_;
goto v_resetjp_2982_;
}
v_resetjp_2982_:
{
lean_object* v_quotContext_2985_; lean_object* v_currMacroScope_2986_; lean_object* v_ref_2987_; uint8_t v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2996_; 
v_quotContext_2985_ = lean_ctor_get(v_a_2961_, 1);
v_currMacroScope_2986_ = lean_ctor_get(v_a_2961_, 2);
v_ref_2987_ = lean_ctor_get(v_a_2961_, 5);
v___x_2988_ = 0;
v___x_2989_ = l_Lean_SourceInfo_fromRef(v_ref_2987_, v___x_2988_);
v___x_2990_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_2991_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertPlainTime___closed__1, &l___private_Std_Time_Notation_0__Std_Time_convertPlainTime___closed__1_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertPlainTime___closed__1);
v___x_2992_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertPlainTime___closed__3));
lean_inc(v_currMacroScope_2986_);
lean_inc(v_quotContext_2985_);
v___x_2993_ = l_Lean_addMacroScope(v_quotContext_2985_, v___x_2992_, v_currMacroScope_2986_);
v___x_2994_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertPlainTime___closed__7));
lean_inc(v___x_2989_);
if (v_isShared_2969_ == 0)
{
lean_ctor_set_tag(v___x_2968_, 3);
lean_ctor_set(v___x_2968_, 3, v___x_2994_);
lean_ctor_set(v___x_2968_, 2, v___x_2993_);
lean_ctor_set(v___x_2968_, 1, v___x_2991_);
lean_ctor_set(v___x_2968_, 0, v___x_2989_);
v___x_2996_ = v___x_2968_;
goto v_reusejp_2995_;
}
else
{
lean_object* v_reuseFailAlloc_3003_; 
v_reuseFailAlloc_3003_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3003_, 0, v___x_2989_);
lean_ctor_set(v_reuseFailAlloc_3003_, 1, v___x_2991_);
lean_ctor_set(v_reuseFailAlloc_3003_, 2, v___x_2993_);
lean_ctor_set(v_reuseFailAlloc_3003_, 3, v___x_2994_);
v___x_2996_ = v_reuseFailAlloc_3003_;
goto v_reusejp_2995_;
}
v_reusejp_2995_:
{
lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3001_; 
v___x_2997_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
lean_inc(v___x_2989_);
v___x_2998_ = l_Lean_Syntax_node4(v___x_2989_, v___x_2997_, v_a_2971_, v_a_2974_, v_a_2977_, v_a_2980_);
v___x_2999_ = l_Lean_Syntax_node2(v___x_2989_, v___x_2990_, v___x_2996_, v___x_2998_);
if (v_isShared_2984_ == 0)
{
lean_ctor_set(v___x_2983_, 0, v___x_2999_);
v___x_3001_ = v___x_2983_;
goto v_reusejp_3000_;
}
else
{
lean_object* v_reuseFailAlloc_3002_; 
v_reuseFailAlloc_3002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3002_, 0, v___x_2999_);
lean_ctor_set(v_reuseFailAlloc_3002_, 1, v_a_2981_);
v___x_3001_ = v_reuseFailAlloc_3002_;
goto v_reusejp_3000_;
}
v_reusejp_3000_:
{
return v___x_3001_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertPlainTime___boxed(lean_object* v_d_3006_, lean_object* v_a_3007_, lean_object* v_a_3008_){
_start:
{
lean_object* v_res_3009_; 
v_res_3009_ = l___private_Std_Time_Notation_0__Std_Time_convertPlainTime(v_d_3006_, v_a_3007_, v_a_3008_);
lean_dec_ref(v_a_3007_);
return v_res_3009_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime___closed__1(void){
_start:
{
lean_object* v___x_3011_; lean_object* v___x_3012_; 
v___x_3011_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime___closed__0));
v___x_3012_ = l_String_toRawSubstring_x27(v___x_3011_);
return v___x_3012_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime(lean_object* v_d_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_){
_start:
{
lean_object* v_date_3033_; lean_object* v_time_3034_; lean_object* v___x_3035_; lean_object* v_a_3036_; lean_object* v_a_3037_; lean_object* v___x_3038_; lean_object* v_a_3039_; lean_object* v_a_3040_; lean_object* v___x_3042_; uint8_t v_isShared_3043_; uint8_t v_isSharedCheck_3061_; 
v_date_3033_ = lean_ctor_get(v_d_3030_, 0);
lean_inc_ref(v_date_3033_);
v_time_3034_ = lean_ctor_get(v_d_3030_, 1);
lean_inc_ref(v_time_3034_);
lean_dec_ref(v_d_3030_);
v___x_3035_ = l___private_Std_Time_Notation_0__Std_Time_convertPlainDate(v_date_3033_, v_a_3031_, v_a_3032_);
lean_dec_ref(v_date_3033_);
v_a_3036_ = lean_ctor_get(v___x_3035_, 0);
lean_inc(v_a_3036_);
v_a_3037_ = lean_ctor_get(v___x_3035_, 1);
lean_inc(v_a_3037_);
lean_dec_ref(v___x_3035_);
v___x_3038_ = l___private_Std_Time_Notation_0__Std_Time_convertPlainTime(v_time_3034_, v_a_3031_, v_a_3037_);
v_a_3039_ = lean_ctor_get(v___x_3038_, 0);
v_a_3040_ = lean_ctor_get(v___x_3038_, 1);
v_isSharedCheck_3061_ = !lean_is_exclusive(v___x_3038_);
if (v_isSharedCheck_3061_ == 0)
{
v___x_3042_ = v___x_3038_;
v_isShared_3043_ = v_isSharedCheck_3061_;
goto v_resetjp_3041_;
}
else
{
lean_inc(v_a_3040_);
lean_inc(v_a_3039_);
lean_dec(v___x_3038_);
v___x_3042_ = lean_box(0);
v_isShared_3043_ = v_isSharedCheck_3061_;
goto v_resetjp_3041_;
}
v_resetjp_3041_:
{
lean_object* v_quotContext_3044_; lean_object* v_currMacroScope_3045_; lean_object* v_ref_3046_; uint8_t v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3059_; 
v_quotContext_3044_ = lean_ctor_get(v_a_3031_, 1);
v_currMacroScope_3045_ = lean_ctor_get(v_a_3031_, 2);
v_ref_3046_ = lean_ctor_get(v_a_3031_, 5);
v___x_3047_ = 0;
v___x_3048_ = l_Lean_SourceInfo_fromRef(v_ref_3046_, v___x_3047_);
v___x_3049_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_3050_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime___closed__1, &l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime___closed__1_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime___closed__1);
v___x_3051_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime___closed__3));
lean_inc(v_currMacroScope_3045_);
lean_inc(v_quotContext_3044_);
v___x_3052_ = l_Lean_addMacroScope(v_quotContext_3044_, v___x_3051_, v_currMacroScope_3045_);
v___x_3053_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime___closed__7));
lean_inc_n(v___x_3048_, 2);
v___x_3054_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3054_, 0, v___x_3048_);
lean_ctor_set(v___x_3054_, 1, v___x_3050_);
lean_ctor_set(v___x_3054_, 2, v___x_3052_);
lean_ctor_set(v___x_3054_, 3, v___x_3053_);
v___x_3055_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_3056_ = l_Lean_Syntax_node2(v___x_3048_, v___x_3055_, v_a_3036_, v_a_3039_);
v___x_3057_ = l_Lean_Syntax_node2(v___x_3048_, v___x_3049_, v___x_3054_, v___x_3056_);
if (v_isShared_3043_ == 0)
{
lean_ctor_set(v___x_3042_, 0, v___x_3057_);
v___x_3059_ = v___x_3042_;
goto v_reusejp_3058_;
}
else
{
lean_object* v_reuseFailAlloc_3060_; 
v_reuseFailAlloc_3060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3060_, 0, v___x_3057_);
lean_ctor_set(v_reuseFailAlloc_3060_, 1, v_a_3040_);
v___x_3059_ = v_reuseFailAlloc_3060_;
goto v_reusejp_3058_;
}
v_reusejp_3058_:
{
return v___x_3059_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime___boxed(lean_object* v_d_3062_, lean_object* v_a_3063_, lean_object* v_a_3064_){
_start:
{
lean_object* v_res_3065_; 
v_res_3065_ = l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime(v_d_3062_, v_a_3063_, v_a_3064_);
lean_dec_ref(v_a_3063_);
return v_res_3065_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__1(void){
_start:
{
lean_object* v___x_3067_; lean_object* v___x_3068_; 
v___x_3067_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__0));
v___x_3068_ = l_String_toRawSubstring_x27(v___x_3067_);
return v___x_3068_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__8(void){
_start:
{
lean_object* v___x_3083_; lean_object* v___x_3084_; 
v___x_3083_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__7));
v___x_3084_ = l_String_toRawSubstring_x27(v___x_3083_);
return v___x_3084_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__21(void){
_start:
{
lean_object* v___x_3111_; lean_object* v___x_3112_; 
v___x_3111_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__20));
v___x_3112_ = l_String_toRawSubstring_x27(v___x_3111_);
return v___x_3112_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime(lean_object* v_d_3119_, uint8_t v_identifier_3120_, lean_object* v_a_3121_, lean_object* v_a_3122_){
_start:
{
lean_object* v_date_3123_; lean_object* v_timezone_3124_; lean_object* v___x_3126_; uint8_t v_isShared_3127_; uint8_t v_isSharedCheck_3218_; 
v_date_3123_ = lean_ctor_get(v_d_3119_, 0);
v_timezone_3124_ = lean_ctor_get(v_d_3119_, 3);
v_isSharedCheck_3218_ = !lean_is_exclusive(v_d_3119_);
if (v_isSharedCheck_3218_ == 0)
{
lean_object* v_unused_3219_; lean_object* v_unused_3220_; 
v_unused_3219_ = lean_ctor_get(v_d_3119_, 2);
lean_dec(v_unused_3219_);
v_unused_3220_ = lean_ctor_get(v_d_3119_, 1);
lean_dec(v_unused_3220_);
v___x_3126_ = v_d_3119_;
v_isShared_3127_ = v_isSharedCheck_3218_;
goto v_resetjp_3125_;
}
else
{
lean_inc(v_timezone_3124_);
lean_inc(v_date_3123_);
lean_dec(v_d_3119_);
v___x_3126_ = lean_box(0);
v_isShared_3127_ = v_isSharedCheck_3218_;
goto v_resetjp_3125_;
}
v_resetjp_3125_:
{
lean_object* v___x_3128_; lean_object* v___x_3129_; 
v___x_3128_ = lean_thunk_get_own(v_date_3123_);
lean_dec_ref(v_date_3123_);
v___x_3129_ = l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime(v___x_3128_, v_a_3121_, v_a_3122_);
if (v_identifier_3120_ == 0)
{
lean_object* v_a_3130_; lean_object* v_a_3131_; lean_object* v___x_3132_; lean_object* v_a_3133_; lean_object* v_a_3134_; lean_object* v___x_3136_; uint8_t v_isShared_3137_; uint8_t v_isSharedCheck_3178_; 
v_a_3130_ = lean_ctor_get(v___x_3129_, 0);
lean_inc(v_a_3130_);
v_a_3131_ = lean_ctor_get(v___x_3129_, 1);
lean_inc(v_a_3131_);
lean_dec_ref(v___x_3129_);
v___x_3132_ = l___private_Std_Time_Notation_0__Std_Time_convertTimezone(v_timezone_3124_, v_a_3121_, v_a_3131_);
v_a_3133_ = lean_ctor_get(v___x_3132_, 0);
v_a_3134_ = lean_ctor_get(v___x_3132_, 1);
v_isSharedCheck_3178_ = !lean_is_exclusive(v___x_3132_);
if (v_isSharedCheck_3178_ == 0)
{
v___x_3136_ = v___x_3132_;
v_isShared_3137_ = v_isSharedCheck_3178_;
goto v_resetjp_3135_;
}
else
{
lean_inc(v_a_3134_);
lean_inc(v_a_3133_);
lean_dec(v___x_3132_);
v___x_3136_ = lean_box(0);
v_isShared_3137_ = v_isSharedCheck_3178_;
goto v_resetjp_3135_;
}
v_resetjp_3135_:
{
lean_object* v_quotContext_3138_; lean_object* v_currMacroScope_3139_; lean_object* v_ref_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3148_; 
v_quotContext_3138_ = lean_ctor_get(v_a_3121_, 1);
v_currMacroScope_3139_ = lean_ctor_get(v_a_3121_, 2);
v_ref_3140_ = lean_ctor_get(v_a_3121_, 5);
v___x_3141_ = l_Lean_SourceInfo_fromRef(v_ref_3140_, v_identifier_3120_);
v___x_3142_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_3143_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__1, &l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__1_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__1);
v___x_3144_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__4));
lean_inc(v_currMacroScope_3139_);
lean_inc(v_quotContext_3138_);
v___x_3145_ = l_Lean_addMacroScope(v_quotContext_3138_, v___x_3144_, v_currMacroScope_3139_);
v___x_3146_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__6));
lean_inc(v___x_3141_);
if (v_isShared_3127_ == 0)
{
lean_ctor_set_tag(v___x_3126_, 3);
lean_ctor_set(v___x_3126_, 3, v___x_3146_);
lean_ctor_set(v___x_3126_, 2, v___x_3145_);
lean_ctor_set(v___x_3126_, 1, v___x_3143_);
lean_ctor_set(v___x_3126_, 0, v___x_3141_);
v___x_3148_ = v___x_3126_;
goto v_reusejp_3147_;
}
else
{
lean_object* v_reuseFailAlloc_3177_; 
v_reuseFailAlloc_3177_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3177_, 0, v___x_3141_);
lean_ctor_set(v_reuseFailAlloc_3177_, 1, v___x_3143_);
lean_ctor_set(v_reuseFailAlloc_3177_, 2, v___x_3145_);
lean_ctor_set(v_reuseFailAlloc_3177_, 3, v___x_3146_);
v___x_3148_ = v_reuseFailAlloc_3177_;
goto v_reusejp_3147_;
}
v_reusejp_3147_:
{
lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3175_; 
v___x_3149_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_3150_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__42));
v___x_3151_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__44));
v___x_3152_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__45));
lean_inc_n(v___x_3141_, 10);
v___x_3153_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3153_, 0, v___x_3141_);
lean_ctor_set(v___x_3153_, 1, v___x_3152_);
v___x_3154_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__47));
v___x_3155_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49, &l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__49);
v___x_3156_ = lean_box(0);
lean_inc_n(v_currMacroScope_3139_, 2);
lean_inc_n(v_quotContext_3138_, 2);
v___x_3157_ = l_Lean_addMacroScope(v_quotContext_3138_, v___x_3156_, v_currMacroScope_3139_);
v___x_3158_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__65));
v___x_3159_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3159_, 0, v___x_3141_);
lean_ctor_set(v___x_3159_, 1, v___x_3155_);
lean_ctor_set(v___x_3159_, 2, v___x_3157_);
lean_ctor_set(v___x_3159_, 3, v___x_3158_);
v___x_3160_ = l_Lean_Syntax_node1(v___x_3141_, v___x_3154_, v___x_3159_);
v___x_3161_ = l_Lean_Syntax_node2(v___x_3141_, v___x_3151_, v___x_3153_, v___x_3160_);
v___x_3162_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__8, &l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__8_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__8);
v___x_3163_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__11));
v___x_3164_ = l_Lean_addMacroScope(v_quotContext_3138_, v___x_3163_, v_currMacroScope_3139_);
v___x_3165_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__13));
v___x_3166_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3166_, 0, v___x_3141_);
lean_ctor_set(v___x_3166_, 1, v___x_3162_);
lean_ctor_set(v___x_3166_, 2, v___x_3164_);
lean_ctor_set(v___x_3166_, 3, v___x_3165_);
v___x_3167_ = l_Lean_Syntax_node1(v___x_3141_, v___x_3149_, v_a_3133_);
v___x_3168_ = l_Lean_Syntax_node2(v___x_3141_, v___x_3142_, v___x_3166_, v___x_3167_);
v___x_3169_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertModifier___closed__72));
v___x_3170_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3170_, 0, v___x_3141_);
lean_ctor_set(v___x_3170_, 1, v___x_3169_);
v___x_3171_ = l_Lean_Syntax_node3(v___x_3141_, v___x_3150_, v___x_3161_, v___x_3168_, v___x_3170_);
v___x_3172_ = l_Lean_Syntax_node2(v___x_3141_, v___x_3149_, v_a_3130_, v___x_3171_);
v___x_3173_ = l_Lean_Syntax_node2(v___x_3141_, v___x_3142_, v___x_3148_, v___x_3172_);
if (v_isShared_3137_ == 0)
{
lean_ctor_set(v___x_3136_, 0, v___x_3173_);
v___x_3175_ = v___x_3136_;
goto v_reusejp_3174_;
}
else
{
lean_object* v_reuseFailAlloc_3176_; 
v_reuseFailAlloc_3176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3176_, 0, v___x_3173_);
lean_ctor_set(v_reuseFailAlloc_3176_, 1, v_a_3134_);
v___x_3175_ = v_reuseFailAlloc_3176_;
goto v_reusejp_3174_;
}
v_reusejp_3174_:
{
return v___x_3175_;
}
}
}
}
else
{
lean_object* v_a_3179_; lean_object* v_a_3180_; lean_object* v___x_3182_; uint8_t v_isShared_3183_; uint8_t v_isSharedCheck_3217_; 
v_a_3179_ = lean_ctor_get(v___x_3129_, 0);
v_a_3180_ = lean_ctor_get(v___x_3129_, 1);
v_isSharedCheck_3217_ = !lean_is_exclusive(v___x_3129_);
if (v_isSharedCheck_3217_ == 0)
{
v___x_3182_ = v___x_3129_;
v_isShared_3183_ = v_isSharedCheck_3217_;
goto v_resetjp_3181_;
}
else
{
lean_inc(v_a_3180_);
lean_inc(v_a_3179_);
lean_dec(v___x_3129_);
v___x_3182_ = lean_box(0);
v_isShared_3183_ = v_isSharedCheck_3217_;
goto v_resetjp_3181_;
}
v_resetjp_3181_:
{
lean_object* v_quotContext_3184_; lean_object* v_currMacroScope_3185_; lean_object* v_ref_3186_; uint8_t v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3195_; 
v_quotContext_3184_ = lean_ctor_get(v_a_3121_, 1);
v_currMacroScope_3185_ = lean_ctor_get(v_a_3121_, 2);
v_ref_3186_ = lean_ctor_get(v_a_3121_, 5);
v___x_3187_ = 0;
v___x_3188_ = l_Lean_SourceInfo_fromRef(v_ref_3186_, v___x_3187_);
v___x_3189_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_3190_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__1, &l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__1_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__1);
v___x_3191_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__4));
lean_inc(v_currMacroScope_3185_);
lean_inc(v_quotContext_3184_);
v___x_3192_ = l_Lean_addMacroScope(v_quotContext_3184_, v___x_3191_, v_currMacroScope_3185_);
v___x_3193_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__6));
lean_inc(v___x_3188_);
if (v_isShared_3127_ == 0)
{
lean_ctor_set_tag(v___x_3126_, 3);
lean_ctor_set(v___x_3126_, 3, v___x_3193_);
lean_ctor_set(v___x_3126_, 2, v___x_3192_);
lean_ctor_set(v___x_3126_, 1, v___x_3190_);
lean_ctor_set(v___x_3126_, 0, v___x_3188_);
v___x_3195_ = v___x_3126_;
goto v_reusejp_3194_;
}
else
{
lean_object* v_reuseFailAlloc_3216_; 
v_reuseFailAlloc_3216_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3216_, 0, v___x_3188_);
lean_ctor_set(v_reuseFailAlloc_3216_, 1, v___x_3190_);
lean_ctor_set(v_reuseFailAlloc_3216_, 2, v___x_3192_);
lean_ctor_set(v_reuseFailAlloc_3216_, 3, v___x_3193_);
v___x_3195_ = v_reuseFailAlloc_3216_;
goto v_reusejp_3194_;
}
v_reusejp_3194_:
{
lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v_name_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3214_; 
v___x_3196_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
lean_inc_n(v___x_3188_, 6);
v___x_3197_ = l_Lean_Syntax_node1(v___x_3188_, v___x_3196_, v_a_3179_);
v___x_3198_ = l_Lean_Syntax_node2(v___x_3188_, v___x_3189_, v___x_3195_, v___x_3197_);
v_name_3199_ = lean_ctor_get(v_timezone_3124_, 1);
lean_inc_ref(v_name_3199_);
lean_dec_ref(v_timezone_3124_);
v___x_3200_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__14));
v___x_3201_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3201_, 0, v___x_3188_);
lean_ctor_set(v___x_3201_, 1, v___x_3200_);
v___x_3202_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__17));
lean_inc(v_currMacroScope_3185_);
lean_inc(v_quotContext_3184_);
v___x_3203_ = l_Lean_addMacroScope(v_quotContext_3184_, v___x_3202_, v_currMacroScope_3185_);
v___x_3204_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__19));
v___x_3205_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__21, &l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__21_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__21);
v___x_3206_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__23));
v___x_3207_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3207_, 0, v___x_3188_);
lean_ctor_set(v___x_3207_, 1, v___x_3205_);
lean_ctor_set(v___x_3207_, 2, v___x_3203_);
lean_ctor_set(v___x_3207_, 3, v___x_3206_);
v___x_3208_ = lean_box(2);
v___x_3209_ = l_Lean_Syntax_mkStrLit(v_name_3199_, v___x_3208_);
v___x_3210_ = l_Lean_Syntax_node1(v___x_3188_, v___x_3196_, v___x_3209_);
v___x_3211_ = l_Lean_Syntax_node2(v___x_3188_, v___x_3189_, v___x_3207_, v___x_3210_);
v___x_3212_ = l_Lean_Syntax_node3(v___x_3188_, v___x_3204_, v___x_3198_, v___x_3201_, v___x_3211_);
if (v_isShared_3183_ == 0)
{
lean_ctor_set(v___x_3182_, 0, v___x_3212_);
v___x_3214_ = v___x_3182_;
goto v_reusejp_3213_;
}
else
{
lean_object* v_reuseFailAlloc_3215_; 
v_reuseFailAlloc_3215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3215_, 0, v___x_3212_);
lean_ctor_set(v_reuseFailAlloc_3215_, 1, v_a_3180_);
v___x_3214_ = v_reuseFailAlloc_3215_;
goto v_reusejp_3213_;
}
v_reusejp_3213_:
{
return v___x_3214_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___boxed(lean_object* v_d_3221_, lean_object* v_identifier_3222_, lean_object* v_a_3223_, lean_object* v_a_3224_){
_start:
{
uint8_t v_identifier_boxed_3225_; lean_object* v_res_3226_; 
v_identifier_boxed_3225_ = lean_unbox(v_identifier_3222_);
v_res_3226_ = l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime(v_d_3221_, v_identifier_boxed_3225_, v_a_3223_, v_a_3224_);
lean_dec_ref(v_a_3223_);
return v_res_3226_;
}
}
LEAN_EXPORT lean_object* l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termZoned_x28___x29__1(lean_object* v_x_3392_, lean_object* v_a_3393_, lean_object* v_a_3394_){
_start:
{
lean_object* v___x_3395_; uint8_t v___x_3396_; 
v___x_3395_ = ((lean_object*)(l_Std_Time_termZoned_x28___x29___closed__1));
lean_inc(v_x_3392_);
v___x_3396_ = l_Lean_Syntax_isOfKind(v_x_3392_, v___x_3395_);
if (v___x_3396_ == 0)
{
lean_object* v___x_3397_; lean_object* v___x_3398_; 
lean_dec(v_x_3392_);
v___x_3397_ = lean_box(1);
v___x_3398_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3398_, 0, v___x_3397_);
lean_ctor_set(v___x_3398_, 1, v_a_3394_);
return v___x_3398_;
}
else
{
lean_object* v___x_3399_; lean_object* v_date_3400_; lean_object* v___x_3401_; uint8_t v___x_3402_; 
v___x_3399_ = lean_unsigned_to_nat(1u);
v_date_3400_ = l_Lean_Syntax_getArg(v_x_3392_, v___x_3399_);
lean_dec(v_x_3392_);
v___x_3401_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxString___closed__1));
lean_inc(v_date_3400_);
v___x_3402_ = l_Lean_Syntax_isOfKind(v_date_3400_, v___x_3401_);
if (v___x_3402_ == 0)
{
lean_object* v___x_3403_; lean_object* v___x_3404_; 
lean_dec(v_date_3400_);
v___x_3403_ = lean_box(1);
v___x_3404_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3404_, 0, v___x_3403_);
lean_ctor_set(v___x_3404_, 1, v_a_3394_);
return v___x_3404_;
}
else
{
lean_object* v___x_3405_; lean_object* v___x_3406_; 
v___x_3405_ = l_Lean_TSyntax_getString(v_date_3400_);
lean_inc_ref(v___x_3405_);
v___x_3406_ = l_Std_Time_ZonedDateTime_fromLeanDateTimeWithZoneString(v___x_3405_);
if (lean_obj_tag(v___x_3406_) == 0)
{
lean_object* v___x_3407_; 
lean_dec_ref(v___x_3406_);
v___x_3407_ = l_Std_Time_ZonedDateTime_fromLeanDateTimeWithIdentifierString(v___x_3405_);
if (lean_obj_tag(v___x_3407_) == 0)
{
lean_object* v_a_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; 
v_a_3408_ = lean_ctor_get(v___x_3407_, 0);
lean_inc(v_a_3408_);
lean_dec_ref(v___x_3407_);
v___x_3409_ = ((lean_object*)(l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termZoned_x28___x29__1___closed__0));
v___x_3410_ = lean_string_append(v___x_3409_, v_a_3408_);
lean_dec(v_a_3408_);
v___x_3411_ = l_Lean_Macro_throwErrorAt___redArg(v_date_3400_, v___x_3410_, v_a_3393_, v_a_3394_);
lean_dec(v_date_3400_);
return v___x_3411_;
}
else
{
lean_object* v_a_3412_; lean_object* v___x_3413_; lean_object* v_a_3414_; lean_object* v_a_3415_; lean_object* v___x_3417_; uint8_t v_isShared_3418_; uint8_t v_isSharedCheck_3422_; 
lean_dec(v_date_3400_);
v_a_3412_ = lean_ctor_get(v___x_3407_, 0);
lean_inc(v_a_3412_);
lean_dec_ref(v___x_3407_);
v___x_3413_ = l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime(v_a_3412_, v___x_3402_, v_a_3393_, v_a_3394_);
v_a_3414_ = lean_ctor_get(v___x_3413_, 0);
v_a_3415_ = lean_ctor_get(v___x_3413_, 1);
v_isSharedCheck_3422_ = !lean_is_exclusive(v___x_3413_);
if (v_isSharedCheck_3422_ == 0)
{
v___x_3417_ = v___x_3413_;
v_isShared_3418_ = v_isSharedCheck_3422_;
goto v_resetjp_3416_;
}
else
{
lean_inc(v_a_3415_);
lean_inc(v_a_3414_);
lean_dec(v___x_3413_);
v___x_3417_ = lean_box(0);
v_isShared_3418_ = v_isSharedCheck_3422_;
goto v_resetjp_3416_;
}
v_resetjp_3416_:
{
lean_object* v___x_3420_; 
if (v_isShared_3418_ == 0)
{
v___x_3420_ = v___x_3417_;
goto v_reusejp_3419_;
}
else
{
lean_object* v_reuseFailAlloc_3421_; 
v_reuseFailAlloc_3421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3421_, 0, v_a_3414_);
lean_ctor_set(v_reuseFailAlloc_3421_, 1, v_a_3415_);
v___x_3420_ = v_reuseFailAlloc_3421_;
goto v_reusejp_3419_;
}
v_reusejp_3419_:
{
return v___x_3420_;
}
}
}
}
else
{
lean_object* v_a_3423_; uint8_t v___x_3424_; lean_object* v___x_3425_; lean_object* v_a_3426_; lean_object* v_a_3427_; lean_object* v___x_3429_; uint8_t v_isShared_3430_; uint8_t v_isSharedCheck_3434_; 
lean_dec_ref(v___x_3405_);
lean_dec(v_date_3400_);
v_a_3423_ = lean_ctor_get(v___x_3406_, 0);
lean_inc(v_a_3423_);
lean_dec_ref(v___x_3406_);
v___x_3424_ = 0;
v___x_3425_ = l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime(v_a_3423_, v___x_3424_, v_a_3393_, v_a_3394_);
v_a_3426_ = lean_ctor_get(v___x_3425_, 0);
v_a_3427_ = lean_ctor_get(v___x_3425_, 1);
v_isSharedCheck_3434_ = !lean_is_exclusive(v___x_3425_);
if (v_isSharedCheck_3434_ == 0)
{
v___x_3429_ = v___x_3425_;
v_isShared_3430_ = v_isSharedCheck_3434_;
goto v_resetjp_3428_;
}
else
{
lean_inc(v_a_3427_);
lean_inc(v_a_3426_);
lean_dec(v___x_3425_);
v___x_3429_ = lean_box(0);
v_isShared_3430_ = v_isSharedCheck_3434_;
goto v_resetjp_3428_;
}
v_resetjp_3428_:
{
lean_object* v___x_3432_; 
if (v_isShared_3430_ == 0)
{
v___x_3432_ = v___x_3429_;
goto v_reusejp_3431_;
}
else
{
lean_object* v_reuseFailAlloc_3433_; 
v_reuseFailAlloc_3433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3433_, 0, v_a_3426_);
lean_ctor_set(v_reuseFailAlloc_3433_, 1, v_a_3427_);
v___x_3432_ = v_reuseFailAlloc_3433_;
goto v_reusejp_3431_;
}
v_reusejp_3431_:
{
return v___x_3432_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termZoned_x28___x29__1___boxed(lean_object* v_x_3435_, lean_object* v_a_3436_, lean_object* v_a_3437_){
_start:
{
lean_object* v_res_3438_; 
v_res_3438_ = l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termZoned_x28___x29__1(v_x_3435_, v_a_3436_, v_a_3437_);
lean_dec_ref(v_a_3436_);
return v_res_3438_;
}
}
LEAN_EXPORT lean_object* l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termZoned_x28___x2c___x29__1(lean_object* v_x_3439_, lean_object* v_a_3440_, lean_object* v_a_3441_){
_start:
{
lean_object* v___x_3442_; uint8_t v___x_3443_; 
v___x_3442_ = ((lean_object*)(l_Std_Time_termZoned_x28___x2c___x29___closed__1));
lean_inc(v_x_3439_);
v___x_3443_ = l_Lean_Syntax_isOfKind(v_x_3439_, v___x_3442_);
if (v___x_3443_ == 0)
{
lean_object* v___x_3444_; lean_object* v___x_3445_; 
lean_dec(v_x_3439_);
v___x_3444_ = lean_box(1);
v___x_3445_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3445_, 0, v___x_3444_);
lean_ctor_set(v___x_3445_, 1, v_a_3441_);
return v___x_3445_;
}
else
{
lean_object* v___x_3446_; lean_object* v_date_3447_; lean_object* v___x_3448_; uint8_t v___x_3449_; 
v___x_3446_ = lean_unsigned_to_nat(1u);
v_date_3447_ = l_Lean_Syntax_getArg(v_x_3439_, v___x_3446_);
v___x_3448_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxString___closed__1));
lean_inc(v_date_3447_);
v___x_3449_ = l_Lean_Syntax_isOfKind(v_date_3447_, v___x_3448_);
if (v___x_3449_ == 0)
{
lean_object* v___x_3450_; lean_object* v___x_3451_; 
lean_dec(v_date_3447_);
lean_dec(v_x_3439_);
v___x_3450_ = lean_box(1);
v___x_3451_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3451_, 0, v___x_3450_);
lean_ctor_set(v___x_3451_, 1, v_a_3441_);
return v___x_3451_;
}
else
{
lean_object* v___x_3452_; lean_object* v___x_3453_; 
v___x_3452_ = l_Lean_TSyntax_getString(v_date_3447_);
v___x_3453_ = l_Std_Time_PlainDateTime_fromLeanDateTimeString(v___x_3452_);
if (lean_obj_tag(v___x_3453_) == 0)
{
lean_object* v_a_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; 
lean_dec(v_x_3439_);
v_a_3454_ = lean_ctor_get(v___x_3453_, 0);
lean_inc(v_a_3454_);
lean_dec_ref(v___x_3453_);
v___x_3455_ = ((lean_object*)(l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termZoned_x28___x29__1___closed__0));
v___x_3456_ = lean_string_append(v___x_3455_, v_a_3454_);
lean_dec(v_a_3454_);
v___x_3457_ = l_Lean_Macro_throwErrorAt___redArg(v_date_3447_, v___x_3456_, v_a_3440_, v_a_3441_);
lean_dec(v_date_3447_);
return v___x_3457_;
}
else
{
lean_object* v_a_3458_; lean_object* v___x_3459_; lean_object* v_a_3460_; lean_object* v_a_3461_; lean_object* v___x_3463_; uint8_t v_isShared_3464_; uint8_t v_isSharedCheck_3484_; 
lean_dec(v_date_3447_);
v_a_3458_ = lean_ctor_get(v___x_3453_, 0);
lean_inc(v_a_3458_);
lean_dec_ref(v___x_3453_);
v___x_3459_ = l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime(v_a_3458_, v_a_3440_, v_a_3441_);
v_a_3460_ = lean_ctor_get(v___x_3459_, 0);
v_a_3461_ = lean_ctor_get(v___x_3459_, 1);
v_isSharedCheck_3484_ = !lean_is_exclusive(v___x_3459_);
if (v_isSharedCheck_3484_ == 0)
{
v___x_3463_ = v___x_3459_;
v_isShared_3464_ = v_isSharedCheck_3484_;
goto v_resetjp_3462_;
}
else
{
lean_inc(v_a_3461_);
lean_inc(v_a_3460_);
lean_dec(v___x_3459_);
v___x_3463_ = lean_box(0);
v_isShared_3464_ = v_isSharedCheck_3484_;
goto v_resetjp_3462_;
}
v_resetjp_3462_:
{
lean_object* v_quotContext_3465_; lean_object* v_currMacroScope_3466_; lean_object* v_ref_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; uint8_t v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3482_; 
v_quotContext_3465_ = lean_ctor_get(v_a_3440_, 1);
v_currMacroScope_3466_ = lean_ctor_get(v_a_3440_, 2);
v_ref_3467_ = lean_ctor_get(v_a_3440_, 5);
v___x_3468_ = lean_unsigned_to_nat(3u);
v___x_3469_ = l_Lean_Syntax_getArg(v_x_3439_, v___x_3468_);
lean_dec(v_x_3439_);
v___x_3470_ = 0;
v___x_3471_ = l_Lean_SourceInfo_fromRef(v_ref_3467_, v___x_3470_);
v___x_3472_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__4));
v___x_3473_ = lean_obj_once(&l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__1, &l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__1_once, _init_l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__1);
v___x_3474_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__4));
lean_inc(v_currMacroScope_3466_);
lean_inc(v_quotContext_3465_);
v___x_3475_ = l_Lean_addMacroScope(v_quotContext_3465_, v___x_3474_, v_currMacroScope_3466_);
v___x_3476_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertZonedDateTime___closed__6));
lean_inc_n(v___x_3471_, 2);
v___x_3477_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3477_, 0, v___x_3471_);
lean_ctor_set(v___x_3477_, 1, v___x_3473_);
lean_ctor_set(v___x_3477_, 2, v___x_3475_);
lean_ctor_set(v___x_3477_, 3, v___x_3476_);
v___x_3478_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_convertNumber___closed__15));
v___x_3479_ = l_Lean_Syntax_node2(v___x_3471_, v___x_3478_, v_a_3460_, v___x_3469_);
v___x_3480_ = l_Lean_Syntax_node2(v___x_3471_, v___x_3472_, v___x_3477_, v___x_3479_);
if (v_isShared_3464_ == 0)
{
lean_ctor_set(v___x_3463_, 0, v___x_3480_);
v___x_3482_ = v___x_3463_;
goto v_reusejp_3481_;
}
else
{
lean_object* v_reuseFailAlloc_3483_; 
v_reuseFailAlloc_3483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3483_, 0, v___x_3480_);
lean_ctor_set(v_reuseFailAlloc_3483_, 1, v_a_3461_);
v___x_3482_ = v_reuseFailAlloc_3483_;
goto v_reusejp_3481_;
}
v_reusejp_3481_:
{
return v___x_3482_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termZoned_x28___x2c___x29__1___boxed(lean_object* v_x_3485_, lean_object* v_a_3486_, lean_object* v_a_3487_){
_start:
{
lean_object* v_res_3488_; 
v_res_3488_ = l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termZoned_x28___x2c___x29__1(v_x_3485_, v_a_3486_, v_a_3487_);
lean_dec_ref(v_a_3486_);
return v_res_3488_;
}
}
LEAN_EXPORT lean_object* l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termDatetime_x28___x29__1(lean_object* v_x_3489_, lean_object* v_a_3490_, lean_object* v_a_3491_){
_start:
{
lean_object* v___x_3492_; uint8_t v___x_3493_; 
v___x_3492_ = ((lean_object*)(l_Std_Time_termDatetime_x28___x29___closed__1));
lean_inc(v_x_3489_);
v___x_3493_ = l_Lean_Syntax_isOfKind(v_x_3489_, v___x_3492_);
if (v___x_3493_ == 0)
{
lean_object* v___x_3494_; lean_object* v___x_3495_; 
lean_dec(v_x_3489_);
v___x_3494_ = lean_box(1);
v___x_3495_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3495_, 0, v___x_3494_);
lean_ctor_set(v___x_3495_, 1, v_a_3491_);
return v___x_3495_;
}
else
{
lean_object* v___x_3496_; lean_object* v_date_3497_; lean_object* v___x_3498_; uint8_t v___x_3499_; 
v___x_3496_ = lean_unsigned_to_nat(1u);
v_date_3497_ = l_Lean_Syntax_getArg(v_x_3489_, v___x_3496_);
lean_dec(v_x_3489_);
v___x_3498_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxString___closed__1));
lean_inc(v_date_3497_);
v___x_3499_ = l_Lean_Syntax_isOfKind(v_date_3497_, v___x_3498_);
if (v___x_3499_ == 0)
{
lean_object* v___x_3500_; lean_object* v___x_3501_; 
lean_dec(v_date_3497_);
v___x_3500_ = lean_box(1);
v___x_3501_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3501_, 0, v___x_3500_);
lean_ctor_set(v___x_3501_, 1, v_a_3491_);
return v___x_3501_;
}
else
{
lean_object* v___x_3502_; lean_object* v___x_3503_; 
v___x_3502_ = l_Lean_TSyntax_getString(v_date_3497_);
v___x_3503_ = l_Std_Time_PlainDateTime_fromLeanDateTimeString(v___x_3502_);
if (lean_obj_tag(v___x_3503_) == 0)
{
lean_object* v_a_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; 
v_a_3504_ = lean_ctor_get(v___x_3503_, 0);
lean_inc(v_a_3504_);
lean_dec_ref(v___x_3503_);
v___x_3505_ = ((lean_object*)(l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termZoned_x28___x29__1___closed__0));
v___x_3506_ = lean_string_append(v___x_3505_, v_a_3504_);
lean_dec(v_a_3504_);
v___x_3507_ = l_Lean_Macro_throwErrorAt___redArg(v_date_3497_, v___x_3506_, v_a_3490_, v_a_3491_);
lean_dec(v_date_3497_);
return v___x_3507_;
}
else
{
lean_object* v_a_3508_; lean_object* v___x_3509_; lean_object* v_a_3510_; lean_object* v_a_3511_; lean_object* v___x_3513_; uint8_t v_isShared_3514_; uint8_t v_isSharedCheck_3518_; 
lean_dec(v_date_3497_);
v_a_3508_ = lean_ctor_get(v___x_3503_, 0);
lean_inc(v_a_3508_);
lean_dec_ref(v___x_3503_);
v___x_3509_ = l___private_Std_Time_Notation_0__Std_Time_convertPlainDateTime(v_a_3508_, v_a_3490_, v_a_3491_);
v_a_3510_ = lean_ctor_get(v___x_3509_, 0);
v_a_3511_ = lean_ctor_get(v___x_3509_, 1);
v_isSharedCheck_3518_ = !lean_is_exclusive(v___x_3509_);
if (v_isSharedCheck_3518_ == 0)
{
v___x_3513_ = v___x_3509_;
v_isShared_3514_ = v_isSharedCheck_3518_;
goto v_resetjp_3512_;
}
else
{
lean_inc(v_a_3511_);
lean_inc(v_a_3510_);
lean_dec(v___x_3509_);
v___x_3513_ = lean_box(0);
v_isShared_3514_ = v_isSharedCheck_3518_;
goto v_resetjp_3512_;
}
v_resetjp_3512_:
{
lean_object* v___x_3516_; 
if (v_isShared_3514_ == 0)
{
v___x_3516_ = v___x_3513_;
goto v_reusejp_3515_;
}
else
{
lean_object* v_reuseFailAlloc_3517_; 
v_reuseFailAlloc_3517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3517_, 0, v_a_3510_);
lean_ctor_set(v_reuseFailAlloc_3517_, 1, v_a_3511_);
v___x_3516_ = v_reuseFailAlloc_3517_;
goto v_reusejp_3515_;
}
v_reusejp_3515_:
{
return v___x_3516_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termDatetime_x28___x29__1___boxed(lean_object* v_x_3519_, lean_object* v_a_3520_, lean_object* v_a_3521_){
_start:
{
lean_object* v_res_3522_; 
v_res_3522_ = l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termDatetime_x28___x29__1(v_x_3519_, v_a_3520_, v_a_3521_);
lean_dec_ref(v_a_3520_);
return v_res_3522_;
}
}
LEAN_EXPORT lean_object* l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termDate_x28___x29__1(lean_object* v_x_3523_, lean_object* v_a_3524_, lean_object* v_a_3525_){
_start:
{
lean_object* v___x_3526_; uint8_t v___x_3527_; 
v___x_3526_ = ((lean_object*)(l_Std_Time_termDate_x28___x29___closed__1));
lean_inc(v_x_3523_);
v___x_3527_ = l_Lean_Syntax_isOfKind(v_x_3523_, v___x_3526_);
if (v___x_3527_ == 0)
{
lean_object* v___x_3528_; lean_object* v___x_3529_; 
lean_dec(v_x_3523_);
v___x_3528_ = lean_box(1);
v___x_3529_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3529_, 0, v___x_3528_);
lean_ctor_set(v___x_3529_, 1, v_a_3525_);
return v___x_3529_;
}
else
{
lean_object* v___x_3530_; lean_object* v_date_3531_; lean_object* v___x_3532_; uint8_t v___x_3533_; 
v___x_3530_ = lean_unsigned_to_nat(1u);
v_date_3531_ = l_Lean_Syntax_getArg(v_x_3523_, v___x_3530_);
lean_dec(v_x_3523_);
v___x_3532_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxString___closed__1));
lean_inc(v_date_3531_);
v___x_3533_ = l_Lean_Syntax_isOfKind(v_date_3531_, v___x_3532_);
if (v___x_3533_ == 0)
{
lean_object* v___x_3534_; lean_object* v___x_3535_; 
lean_dec(v_date_3531_);
v___x_3534_ = lean_box(1);
v___x_3535_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3535_, 0, v___x_3534_);
lean_ctor_set(v___x_3535_, 1, v_a_3525_);
return v___x_3535_;
}
else
{
lean_object* v___x_3536_; lean_object* v___x_3537_; 
v___x_3536_ = l_Lean_TSyntax_getString(v_date_3531_);
v___x_3537_ = l_Std_Time_PlainDate_fromSQLDateString(v___x_3536_);
if (lean_obj_tag(v___x_3537_) == 0)
{
lean_object* v_a_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; 
v_a_3538_ = lean_ctor_get(v___x_3537_, 0);
lean_inc(v_a_3538_);
lean_dec_ref(v___x_3537_);
v___x_3539_ = ((lean_object*)(l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termZoned_x28___x29__1___closed__0));
v___x_3540_ = lean_string_append(v___x_3539_, v_a_3538_);
lean_dec(v_a_3538_);
v___x_3541_ = l_Lean_Macro_throwErrorAt___redArg(v_date_3531_, v___x_3540_, v_a_3524_, v_a_3525_);
lean_dec(v_date_3531_);
return v___x_3541_;
}
else
{
lean_object* v_a_3542_; lean_object* v___x_3543_; lean_object* v_a_3544_; lean_object* v_a_3545_; lean_object* v___x_3547_; uint8_t v_isShared_3548_; uint8_t v_isSharedCheck_3552_; 
lean_dec(v_date_3531_);
v_a_3542_ = lean_ctor_get(v___x_3537_, 0);
lean_inc(v_a_3542_);
lean_dec_ref(v___x_3537_);
v___x_3543_ = l___private_Std_Time_Notation_0__Std_Time_convertPlainDate(v_a_3542_, v_a_3524_, v_a_3525_);
lean_dec(v_a_3542_);
v_a_3544_ = lean_ctor_get(v___x_3543_, 0);
v_a_3545_ = lean_ctor_get(v___x_3543_, 1);
v_isSharedCheck_3552_ = !lean_is_exclusive(v___x_3543_);
if (v_isSharedCheck_3552_ == 0)
{
v___x_3547_ = v___x_3543_;
v_isShared_3548_ = v_isSharedCheck_3552_;
goto v_resetjp_3546_;
}
else
{
lean_inc(v_a_3545_);
lean_inc(v_a_3544_);
lean_dec(v___x_3543_);
v___x_3547_ = lean_box(0);
v_isShared_3548_ = v_isSharedCheck_3552_;
goto v_resetjp_3546_;
}
v_resetjp_3546_:
{
lean_object* v___x_3550_; 
if (v_isShared_3548_ == 0)
{
v___x_3550_ = v___x_3547_;
goto v_reusejp_3549_;
}
else
{
lean_object* v_reuseFailAlloc_3551_; 
v_reuseFailAlloc_3551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3551_, 0, v_a_3544_);
lean_ctor_set(v_reuseFailAlloc_3551_, 1, v_a_3545_);
v___x_3550_ = v_reuseFailAlloc_3551_;
goto v_reusejp_3549_;
}
v_reusejp_3549_:
{
return v___x_3550_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termDate_x28___x29__1___boxed(lean_object* v_x_3553_, lean_object* v_a_3554_, lean_object* v_a_3555_){
_start:
{
lean_object* v_res_3556_; 
v_res_3556_ = l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termDate_x28___x29__1(v_x_3553_, v_a_3554_, v_a_3555_);
lean_dec_ref(v_a_3554_);
return v_res_3556_;
}
}
LEAN_EXPORT lean_object* l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termTime_x28___x29__1(lean_object* v_x_3557_, lean_object* v_a_3558_, lean_object* v_a_3559_){
_start:
{
lean_object* v___x_3560_; uint8_t v___x_3561_; 
v___x_3560_ = ((lean_object*)(l_Std_Time_termTime_x28___x29___closed__1));
lean_inc(v_x_3557_);
v___x_3561_ = l_Lean_Syntax_isOfKind(v_x_3557_, v___x_3560_);
if (v___x_3561_ == 0)
{
lean_object* v___x_3562_; lean_object* v___x_3563_; 
lean_dec(v_x_3557_);
v___x_3562_ = lean_box(1);
v___x_3563_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3563_, 0, v___x_3562_);
lean_ctor_set(v___x_3563_, 1, v_a_3559_);
return v___x_3563_;
}
else
{
lean_object* v___x_3564_; lean_object* v_time_3565_; lean_object* v___x_3566_; uint8_t v___x_3567_; 
v___x_3564_ = lean_unsigned_to_nat(1u);
v_time_3565_ = l_Lean_Syntax_getArg(v_x_3557_, v___x_3564_);
lean_dec(v_x_3557_);
v___x_3566_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxString___closed__1));
lean_inc(v_time_3565_);
v___x_3567_ = l_Lean_Syntax_isOfKind(v_time_3565_, v___x_3566_);
if (v___x_3567_ == 0)
{
lean_object* v___x_3568_; lean_object* v___x_3569_; 
lean_dec(v_time_3565_);
v___x_3568_ = lean_box(1);
v___x_3569_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3569_, 0, v___x_3568_);
lean_ctor_set(v___x_3569_, 1, v_a_3559_);
return v___x_3569_;
}
else
{
lean_object* v___x_3570_; lean_object* v___x_3571_; 
v___x_3570_ = l_Lean_TSyntax_getString(v_time_3565_);
v___x_3571_ = l_Std_Time_PlainTime_fromLeanTime24Hour(v___x_3570_);
if (lean_obj_tag(v___x_3571_) == 0)
{
lean_object* v_a_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; 
v_a_3572_ = lean_ctor_get(v___x_3571_, 0);
lean_inc(v_a_3572_);
lean_dec_ref(v___x_3571_);
v___x_3573_ = ((lean_object*)(l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termZoned_x28___x29__1___closed__0));
v___x_3574_ = lean_string_append(v___x_3573_, v_a_3572_);
lean_dec(v_a_3572_);
v___x_3575_ = l_Lean_Macro_throwErrorAt___redArg(v_time_3565_, v___x_3574_, v_a_3558_, v_a_3559_);
lean_dec(v_time_3565_);
return v___x_3575_;
}
else
{
lean_object* v_a_3576_; lean_object* v___x_3577_; lean_object* v_a_3578_; lean_object* v_a_3579_; lean_object* v___x_3581_; uint8_t v_isShared_3582_; uint8_t v_isSharedCheck_3586_; 
lean_dec(v_time_3565_);
v_a_3576_ = lean_ctor_get(v___x_3571_, 0);
lean_inc(v_a_3576_);
lean_dec_ref(v___x_3571_);
v___x_3577_ = l___private_Std_Time_Notation_0__Std_Time_convertPlainTime(v_a_3576_, v_a_3558_, v_a_3559_);
v_a_3578_ = lean_ctor_get(v___x_3577_, 0);
v_a_3579_ = lean_ctor_get(v___x_3577_, 1);
v_isSharedCheck_3586_ = !lean_is_exclusive(v___x_3577_);
if (v_isSharedCheck_3586_ == 0)
{
v___x_3581_ = v___x_3577_;
v_isShared_3582_ = v_isSharedCheck_3586_;
goto v_resetjp_3580_;
}
else
{
lean_inc(v_a_3579_);
lean_inc(v_a_3578_);
lean_dec(v___x_3577_);
v___x_3581_ = lean_box(0);
v_isShared_3582_ = v_isSharedCheck_3586_;
goto v_resetjp_3580_;
}
v_resetjp_3580_:
{
lean_object* v___x_3584_; 
if (v_isShared_3582_ == 0)
{
v___x_3584_ = v___x_3581_;
goto v_reusejp_3583_;
}
else
{
lean_object* v_reuseFailAlloc_3585_; 
v_reuseFailAlloc_3585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3585_, 0, v_a_3578_);
lean_ctor_set(v_reuseFailAlloc_3585_, 1, v_a_3579_);
v___x_3584_ = v_reuseFailAlloc_3585_;
goto v_reusejp_3583_;
}
v_reusejp_3583_:
{
return v___x_3584_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termTime_x28___x29__1___boxed(lean_object* v_x_3587_, lean_object* v_a_3588_, lean_object* v_a_3589_){
_start:
{
lean_object* v_res_3590_; 
v_res_3590_ = l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termTime_x28___x29__1(v_x_3587_, v_a_3588_, v_a_3589_);
lean_dec_ref(v_a_3588_);
return v_res_3590_;
}
}
LEAN_EXPORT lean_object* l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termOffset_x28___x29__1(lean_object* v_x_3591_, lean_object* v_a_3592_, lean_object* v_a_3593_){
_start:
{
lean_object* v___x_3594_; uint8_t v___x_3595_; 
v___x_3594_ = ((lean_object*)(l_Std_Time_termOffset_x28___x29___closed__1));
lean_inc(v_x_3591_);
v___x_3595_ = l_Lean_Syntax_isOfKind(v_x_3591_, v___x_3594_);
if (v___x_3595_ == 0)
{
lean_object* v___x_3596_; lean_object* v___x_3597_; 
lean_dec(v_x_3591_);
v___x_3596_ = lean_box(1);
v___x_3597_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3597_, 0, v___x_3596_);
lean_ctor_set(v___x_3597_, 1, v_a_3593_);
return v___x_3597_;
}
else
{
lean_object* v___x_3598_; lean_object* v_offset_3599_; lean_object* v___x_3600_; uint8_t v___x_3601_; 
v___x_3598_ = lean_unsigned_to_nat(1u);
v_offset_3599_ = l_Lean_Syntax_getArg(v_x_3591_, v___x_3598_);
lean_dec(v_x_3591_);
v___x_3600_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxString___closed__1));
lean_inc(v_offset_3599_);
v___x_3601_ = l_Lean_Syntax_isOfKind(v_offset_3599_, v___x_3600_);
if (v___x_3601_ == 0)
{
lean_object* v___x_3602_; lean_object* v___x_3603_; 
lean_dec(v_offset_3599_);
v___x_3602_ = lean_box(1);
v___x_3603_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3603_, 0, v___x_3602_);
lean_ctor_set(v___x_3603_, 1, v_a_3593_);
return v___x_3603_;
}
else
{
lean_object* v___x_3604_; lean_object* v___x_3605_; 
v___x_3604_ = l_Lean_TSyntax_getString(v_offset_3599_);
v___x_3605_ = l_Std_Time_TimeZone_Offset_fromOffset(v___x_3604_);
if (lean_obj_tag(v___x_3605_) == 0)
{
lean_object* v_a_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; 
v_a_3606_ = lean_ctor_get(v___x_3605_, 0);
lean_inc(v_a_3606_);
lean_dec_ref(v___x_3605_);
v___x_3607_ = ((lean_object*)(l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termZoned_x28___x29__1___closed__0));
v___x_3608_ = lean_string_append(v___x_3607_, v_a_3606_);
lean_dec(v_a_3606_);
v___x_3609_ = l_Lean_Macro_throwErrorAt___redArg(v_offset_3599_, v___x_3608_, v_a_3592_, v_a_3593_);
lean_dec(v_offset_3599_);
return v___x_3609_;
}
else
{
lean_object* v_a_3610_; lean_object* v___x_3611_; lean_object* v_a_3612_; lean_object* v_a_3613_; lean_object* v___x_3615_; uint8_t v_isShared_3616_; uint8_t v_isSharedCheck_3620_; 
lean_dec(v_offset_3599_);
v_a_3610_ = lean_ctor_get(v___x_3605_, 0);
lean_inc(v_a_3610_);
lean_dec_ref(v___x_3605_);
v___x_3611_ = l___private_Std_Time_Notation_0__Std_Time_convertOffset(v_a_3610_, v_a_3592_, v_a_3593_);
lean_dec(v_a_3610_);
v_a_3612_ = lean_ctor_get(v___x_3611_, 0);
v_a_3613_ = lean_ctor_get(v___x_3611_, 1);
v_isSharedCheck_3620_ = !lean_is_exclusive(v___x_3611_);
if (v_isSharedCheck_3620_ == 0)
{
v___x_3615_ = v___x_3611_;
v_isShared_3616_ = v_isSharedCheck_3620_;
goto v_resetjp_3614_;
}
else
{
lean_inc(v_a_3613_);
lean_inc(v_a_3612_);
lean_dec(v___x_3611_);
v___x_3615_ = lean_box(0);
v_isShared_3616_ = v_isSharedCheck_3620_;
goto v_resetjp_3614_;
}
v_resetjp_3614_:
{
lean_object* v___x_3618_; 
if (v_isShared_3616_ == 0)
{
v___x_3618_ = v___x_3615_;
goto v_reusejp_3617_;
}
else
{
lean_object* v_reuseFailAlloc_3619_; 
v_reuseFailAlloc_3619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3619_, 0, v_a_3612_);
lean_ctor_set(v_reuseFailAlloc_3619_, 1, v_a_3613_);
v___x_3618_ = v_reuseFailAlloc_3619_;
goto v_reusejp_3617_;
}
v_reusejp_3617_:
{
return v___x_3618_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termOffset_x28___x29__1___boxed(lean_object* v_x_3621_, lean_object* v_a_3622_, lean_object* v_a_3623_){
_start:
{
lean_object* v_res_3624_; 
v_res_3624_ = l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termOffset_x28___x29__1(v_x_3621_, v_a_3622_, v_a_3623_);
lean_dec_ref(v_a_3622_);
return v_res_3624_;
}
}
LEAN_EXPORT lean_object* l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termTimezone_x28___x29__1(lean_object* v_x_3625_, lean_object* v_a_3626_, lean_object* v_a_3627_){
_start:
{
lean_object* v___x_3628_; uint8_t v___x_3629_; 
v___x_3628_ = ((lean_object*)(l_Std_Time_termTimezone_x28___x29___closed__1));
lean_inc(v_x_3625_);
v___x_3629_ = l_Lean_Syntax_isOfKind(v_x_3625_, v___x_3628_);
if (v___x_3629_ == 0)
{
lean_object* v___x_3630_; lean_object* v___x_3631_; 
lean_dec(v_x_3625_);
v___x_3630_ = lean_box(1);
v___x_3631_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3631_, 0, v___x_3630_);
lean_ctor_set(v___x_3631_, 1, v_a_3627_);
return v___x_3631_;
}
else
{
lean_object* v___x_3632_; lean_object* v_tz_3633_; lean_object* v___x_3634_; uint8_t v___x_3635_; 
v___x_3632_ = lean_unsigned_to_nat(1u);
v_tz_3633_ = l_Lean_Syntax_getArg(v_x_3625_, v___x_3632_);
lean_dec(v_x_3625_);
v___x_3634_ = ((lean_object*)(l___private_Std_Time_Notation_0__Std_Time_syntaxString___closed__1));
lean_inc(v_tz_3633_);
v___x_3635_ = l_Lean_Syntax_isOfKind(v_tz_3633_, v___x_3634_);
if (v___x_3635_ == 0)
{
lean_object* v___x_3636_; lean_object* v___x_3637_; 
lean_dec(v_tz_3633_);
v___x_3636_ = lean_box(1);
v___x_3637_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3637_, 0, v___x_3636_);
lean_ctor_set(v___x_3637_, 1, v_a_3627_);
return v___x_3637_;
}
else
{
lean_object* v___x_3638_; lean_object* v___x_3639_; 
v___x_3638_ = l_Lean_TSyntax_getString(v_tz_3633_);
v___x_3639_ = l_Std_Time_TimeZone_fromTimeZone(v___x_3638_);
if (lean_obj_tag(v___x_3639_) == 0)
{
lean_object* v_a_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; 
v_a_3640_ = lean_ctor_get(v___x_3639_, 0);
lean_inc(v_a_3640_);
lean_dec_ref(v___x_3639_);
v___x_3641_ = ((lean_object*)(l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termZoned_x28___x29__1___closed__0));
v___x_3642_ = lean_string_append(v___x_3641_, v_a_3640_);
lean_dec(v_a_3640_);
v___x_3643_ = l_Lean_Macro_throwErrorAt___redArg(v_tz_3633_, v___x_3642_, v_a_3626_, v_a_3627_);
lean_dec(v_tz_3633_);
return v___x_3643_;
}
else
{
lean_object* v_a_3644_; lean_object* v___x_3645_; lean_object* v_a_3646_; lean_object* v_a_3647_; lean_object* v___x_3649_; uint8_t v_isShared_3650_; uint8_t v_isSharedCheck_3654_; 
lean_dec(v_tz_3633_);
v_a_3644_ = lean_ctor_get(v___x_3639_, 0);
lean_inc(v_a_3644_);
lean_dec_ref(v___x_3639_);
v___x_3645_ = l___private_Std_Time_Notation_0__Std_Time_convertTimezone(v_a_3644_, v_a_3626_, v_a_3627_);
v_a_3646_ = lean_ctor_get(v___x_3645_, 0);
v_a_3647_ = lean_ctor_get(v___x_3645_, 1);
v_isSharedCheck_3654_ = !lean_is_exclusive(v___x_3645_);
if (v_isSharedCheck_3654_ == 0)
{
v___x_3649_ = v___x_3645_;
v_isShared_3650_ = v_isSharedCheck_3654_;
goto v_resetjp_3648_;
}
else
{
lean_inc(v_a_3647_);
lean_inc(v_a_3646_);
lean_dec(v___x_3645_);
v___x_3649_ = lean_box(0);
v_isShared_3650_ = v_isSharedCheck_3654_;
goto v_resetjp_3648_;
}
v_resetjp_3648_:
{
lean_object* v___x_3652_; 
if (v_isShared_3650_ == 0)
{
v___x_3652_ = v___x_3649_;
goto v_reusejp_3651_;
}
else
{
lean_object* v_reuseFailAlloc_3653_; 
v_reuseFailAlloc_3653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3653_, 0, v_a_3646_);
lean_ctor_set(v_reuseFailAlloc_3653_, 1, v_a_3647_);
v___x_3652_ = v_reuseFailAlloc_3653_;
goto v_reusejp_3651_;
}
v_reusejp_3651_:
{
return v___x_3652_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termTimezone_x28___x29__1___boxed(lean_object* v_x_3655_, lean_object* v_a_3656_, lean_object* v_a_3657_){
_start:
{
lean_object* v_res_3658_; 
v_res_3658_ = l_Std_Time___aux__Std__Time__Notation______macroRules__Std__Time__termTimezone_x28___x29__1(v_x_3655_, v_a_3656_, v_a_3657_);
lean_dec_ref(v_a_3656_);
return v_res_3658_;
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

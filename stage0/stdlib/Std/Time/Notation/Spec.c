// Lean compiler output
// Module: Std.Time.Notation.Spec
// Imports: public import Std.Time.Format.Basic public meta import Std.Time.Format.Basic
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
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Syntax_mkNumLit(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getString(lean_object*);
extern lean_object* l_Std_Time_DateFormat_enUS;
lean_object* l_Std_Time_GenericFormat_spec___redArg(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Syntax_mkStrLit(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_TSepArray_push___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Text.short"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__0 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__0_value;
static lean_once_cell_t l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__1;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Time"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Text"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__4 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__4_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "short"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__5 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__5_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__6_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__6_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__4_value),LEAN_SCALAR_PTR_LITERAL(173, 214, 90, 117, 56, 8, 198, 188)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__6_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__5_value),LEAN_SCALAR_PTR_LITERAL(26, 39, 135, 112, 213, 217, 93, 143)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__6 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__6_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__7 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__7_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__6_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__8 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__8_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__9 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__9_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__7_value),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__9_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__10 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__10_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Std.Time.Text.full"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__11 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__11_value;
static lean_once_cell_t l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__12;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "full"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__13 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__13_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__14_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__14_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__4_value),LEAN_SCALAR_PTR_LITERAL(173, 214, 90, 117, 56, 8, 198, 188)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__14_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__13_value),LEAN_SCALAR_PTR_LITERAL(249, 161, 82, 63, 128, 99, 134, 35)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__14 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__14_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__14_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__15 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__15_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__14_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__16 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__16_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__16_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__17 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__17_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__15_value),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__17_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__18 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__18_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Std.Time.Text.narrow"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__19 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__19_value;
static lean_once_cell_t l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__20;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "narrow"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__21 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__21_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__22_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__22_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__22_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__22_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__4_value),LEAN_SCALAR_PTR_LITERAL(173, 214, 90, 117, 56, 8, 198, 188)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__22_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__21_value),LEAN_SCALAR_PTR_LITERAL(222, 165, 179, 214, 155, 106, 191, 242)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__22 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__22_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__22_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__23 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__23_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__22_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__24 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__24_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__24_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__25 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__25_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__23_value),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__25_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__26 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__26_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Std.Time.Text.twoLetterShort"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__27 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__27_value;
static lean_once_cell_t l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__28;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "twoLetterShort"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__29 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__29_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__30_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__30_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__30_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__30_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__4_value),LEAN_SCALAR_PTR_LITERAL(173, 214, 90, 117, 56, 8, 198, 188)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__30_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__29_value),LEAN_SCALAR_PTR_LITERAL(168, 63, 137, 16, 74, 20, 200, 159)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__30 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__30_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__30_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__31 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__31_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__30_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__32 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__32_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__32_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__33 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__33_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__31_value),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__33_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__34 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__34_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertText(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__0 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__0_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__1 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__1_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__2 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__2_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__3 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__3_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__3_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Std.Time.Number.mk"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__5 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__5_value;
static lean_once_cell_t l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__6;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Number"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__7 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__7_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__8 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__8_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__9_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__9_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__7_value),LEAN_SCALAR_PTR_LITERAL(149, 31, 30, 146, 171, 66, 77, 169)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__9_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__8_value),LEAN_SCALAR_PTR_LITERAL(17, 215, 130, 19, 65, 152, 2, 206)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__9 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__9_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__10 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__10_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__9_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__11 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__11_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__11_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__12 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__12_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__10_value),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__12_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__13 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__13_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__14 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__14_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__14_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Std.Time.Fraction.nano"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__0 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__0_value;
static lean_once_cell_t l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__1;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Fraction"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__2 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__2_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "nano"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__3 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__3_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__4_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__4_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(174, 147, 200, 1, 236, 88, 4, 2)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__4_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__3_value),LEAN_SCALAR_PTR_LITERAL(135, 130, 55, 186, 177, 120, 199, 35)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__4 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__4_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__5 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__5_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__4_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__6 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__6_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__7 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__7_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__5_value),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__7_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__8 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__8_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Std.Time.Fraction.truncated"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__9 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__9_value;
static lean_once_cell_t l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__10;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "truncated"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__11 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__11_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__12_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__12_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(174, 147, 200, 1, 236, 88, 4, 2)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__12_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__11_value),LEAN_SCALAR_PTR_LITERAL(245, 244, 158, 231, 210, 230, 8, 254)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__12 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__12_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__12_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__13 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__13_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__12_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__14 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__14_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__14_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__15 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__15_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__13_value),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__15_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__16 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__16_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Std.Time.Year.any"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__0 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__0_value;
static lean_once_cell_t l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__1;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Year"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__2 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__2_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "any"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__3 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__3_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__4_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__4_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__2_value),LEAN_SCALAR_PTR_LITERAL(81, 61, 104, 127, 147, 223, 116, 59)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__4_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__3_value),LEAN_SCALAR_PTR_LITERAL(177, 87, 37, 32, 28, 199, 229, 134)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__4 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__4_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__5 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__5_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__4_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__6 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__6_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__7 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__7_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__5_value),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__7_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__8 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__8_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Std.Time.Year.twoDigit"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__9 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__9_value;
static lean_once_cell_t l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__10;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "twoDigit"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__11 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__11_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__12_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__12_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__2_value),LEAN_SCALAR_PTR_LITERAL(81, 61, 104, 127, 147, 223, 116, 59)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__12_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__11_value),LEAN_SCALAR_PTR_LITERAL(10, 27, 61, 34, 208, 129, 36, 157)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__12 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__12_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__12_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__13 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__13_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__12_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__14 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__14_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__14_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__15 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__15_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__13_value),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__15_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__16 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__16_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Std.Time.Year.fourDigit"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__17 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__17_value;
static lean_once_cell_t l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__18;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "fourDigit"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__19 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__19_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__20_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__20_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__2_value),LEAN_SCALAR_PTR_LITERAL(81, 61, 104, 127, 147, 223, 116, 59)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__20_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__19_value),LEAN_SCALAR_PTR_LITERAL(251, 28, 132, 113, 104, 79, 27, 228)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__20 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__20_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__20_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__21 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__21_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__20_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__22 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__22_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__22_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__23 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__23_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__21_value),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__23_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__24 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__24_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Std.Time.Year.extended"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__25 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__25_value;
static lean_once_cell_t l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__26;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "extended"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__27 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__27_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__28_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__28_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__28_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__28_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__2_value),LEAN_SCALAR_PTR_LITERAL(81, 61, 104, 127, 147, 223, 116, 59)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__28_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__27_value),LEAN_SCALAR_PTR_LITERAL(173, 52, 201, 124, 50, 137, 219, 209)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__28 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__28_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__28_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__29 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__29_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__28_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__30 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__30_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__30_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__31 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__31_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__29_value),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__31_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__32 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__32_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Std.Time.ZoneId.unknown"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__0 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__0_value;
static lean_once_cell_t l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__1;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ZoneId"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__2 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__2_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "unknown"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__3 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__3_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__4_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__4_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__2_value),LEAN_SCALAR_PTR_LITERAL(15, 155, 217, 32, 218, 79, 133, 226)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__4_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__3_value),LEAN_SCALAR_PTR_LITERAL(81, 61, 96, 224, 240, 156, 239, 4)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__4 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__4_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__5 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__5_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__4_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__6 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__6_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__7 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__7_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__5_value),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__7_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__8 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__8_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Std.Time.ZoneId.short"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__9 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__9_value;
static lean_once_cell_t l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__10;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__11_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__11_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__2_value),LEAN_SCALAR_PTR_LITERAL(15, 155, 217, 32, 218, 79, 133, 226)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__11_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__5_value),LEAN_SCALAR_PTR_LITERAL(208, 236, 57, 76, 90, 0, 9, 31)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__11 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__11_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__11_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__12 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__12_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__11_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__13 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__13_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__13_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__14 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__14_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__12_value),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__14_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__15 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__15_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Std.Time.ZoneId.full"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__16 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__16_value;
static lean_once_cell_t l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__17;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__18_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__18_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__2_value),LEAN_SCALAR_PTR_LITERAL(15, 155, 217, 32, 218, 79, 133, 226)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__18_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__13_value),LEAN_SCALAR_PTR_LITERAL(67, 92, 171, 27, 57, 53, 132, 168)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__18 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__18_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__18_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__19 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__19_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__18_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__20 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__20_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__20_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__21 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__21_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__19_value),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__21_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__22 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__22_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Std.Time.ZoneName.short"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__0 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__0_value;
static lean_once_cell_t l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__1;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ZoneName"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__2 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__2_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__3_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__3_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 221, 249, 71, 196, 230, 130, 14)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__3_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__5_value),LEAN_SCALAR_PTR_LITERAL(48, 208, 46, 14, 98, 17, 211, 187)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__3 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__3_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__4 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__4_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__3_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__5 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__5_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__6 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__6_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__4_value),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__6_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__7 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__7_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Std.Time.ZoneName.full"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__8 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__8_value;
static lean_once_cell_t l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__9;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__10_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__10_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 221, 249, 71, 196, 230, 130, 14)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__10_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__13_value),LEAN_SCALAR_PTR_LITERAL(227, 76, 103, 143, 218, 9, 212, 240)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__10 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__10_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__11 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__11_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__10_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__12 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__12_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__12_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__13 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__13_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__11_value),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__13_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__14 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__14_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Std.Time.OffsetX.hour"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__0 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__0_value;
static lean_once_cell_t l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__1;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "OffsetX"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__2 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__2_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hour"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__3 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__3_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__4_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__4_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__2_value),LEAN_SCALAR_PTR_LITERAL(72, 17, 42, 12, 20, 221, 211, 164)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__4_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__3_value),LEAN_SCALAR_PTR_LITERAL(94, 128, 73, 10, 93, 38, 17, 147)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__4 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__4_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__5 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__5_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__4_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__6 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__6_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__7 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__7_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__5_value),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__7_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__8 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__8_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Std.Time.OffsetX.hourMinute"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__9 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__9_value;
static lean_once_cell_t l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__10;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "hourMinute"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__11 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__11_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__12_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__12_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__2_value),LEAN_SCALAR_PTR_LITERAL(72, 17, 42, 12, 20, 221, 211, 164)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__12_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__11_value),LEAN_SCALAR_PTR_LITERAL(224, 164, 8, 144, 244, 85, 185, 49)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__12 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__12_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__12_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__13 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__13_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__12_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__14 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__14_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__14_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__15 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__15_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__13_value),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__15_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__16 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__16_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Std.Time.OffsetX.hourMinuteColon"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__17 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__17_value;
static lean_once_cell_t l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__18;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "hourMinuteColon"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__19 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__19_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__20_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__20_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__2_value),LEAN_SCALAR_PTR_LITERAL(72, 17, 42, 12, 20, 221, 211, 164)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__20_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__19_value),LEAN_SCALAR_PTR_LITERAL(41, 14, 191, 247, 70, 78, 152, 94)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__20 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__20_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__20_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__21 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__21_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__20_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__22 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__22_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__22_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__23 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__23_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__21_value),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__23_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__24 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__24_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Std.Time.OffsetX.hourMinuteSecond"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__25 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__25_value;
static lean_once_cell_t l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__26;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "hourMinuteSecond"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__27 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__27_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__28_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__28_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__28_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__28_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__2_value),LEAN_SCALAR_PTR_LITERAL(72, 17, 42, 12, 20, 221, 211, 164)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__28_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__27_value),LEAN_SCALAR_PTR_LITERAL(225, 206, 103, 171, 252, 66, 132, 235)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__28 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__28_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__28_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__29 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__29_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__28_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__30 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__30_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__30_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__31 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__31_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__29_value),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__31_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__32 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__32_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "Std.Time.OffsetX.hourMinuteSecondColon"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__33 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__33_value;
static lean_once_cell_t l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__34;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "hourMinuteSecondColon"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__35 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__35_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__36_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__36_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__36_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__36_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__36_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__2_value),LEAN_SCALAR_PTR_LITERAL(72, 17, 42, 12, 20, 221, 211, 164)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__36_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__35_value),LEAN_SCALAR_PTR_LITERAL(140, 30, 191, 40, 228, 93, 219, 98)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__36 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__36_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__36_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__37 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__37_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__36_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__38 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__38_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__38_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__39 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__39_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__37_value),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__39_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__40 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__40_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Std.Time.OffsetO.short"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__0 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__0_value;
static lean_once_cell_t l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__1;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "OffsetO"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__2 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__2_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__3_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__3_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__2_value),LEAN_SCALAR_PTR_LITERAL(67, 124, 82, 133, 197, 108, 218, 207)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__3_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__5_value),LEAN_SCALAR_PTR_LITERAL(12, 166, 178, 82, 100, 100, 15, 194)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__3 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__3_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__4 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__4_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__3_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__5 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__5_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__6 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__6_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__4_value),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__6_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__7 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__7_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Std.Time.OffsetO.full"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__8 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__8_value;
static lean_once_cell_t l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__9;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__10_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__10_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__2_value),LEAN_SCALAR_PTR_LITERAL(67, 124, 82, 133, 197, 108, 218, 207)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__10_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__13_value),LEAN_SCALAR_PTR_LITERAL(87, 208, 214, 192, 175, 181, 101, 171)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__10 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__10_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__11 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__11_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__10_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__12 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__12_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__12_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__13 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__13_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__11_value),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__13_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__14 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__14_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Std.Time.OffsetZ.hourMinute"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__0 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__0_value;
static lean_once_cell_t l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__1;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "OffsetZ"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__2 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__2_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__3_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__3_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__2_value),LEAN_SCALAR_PTR_LITERAL(165, 154, 120, 218, 15, 36, 228, 254)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__3_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__11_value),LEAN_SCALAR_PTR_LITERAL(17, 33, 135, 180, 146, 21, 133, 89)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__3 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__3_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__4 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__4_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__3_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__5 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__5_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__6 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__6_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__4_value),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__6_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__7 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__7_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Std.Time.OffsetZ.full"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__8 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__8_value;
static lean_once_cell_t l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__9;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__10_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__10_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__2_value),LEAN_SCALAR_PTR_LITERAL(165, 154, 120, 218, 15, 36, 228, 254)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__10_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__13_value),LEAN_SCALAR_PTR_LITERAL(161, 2, 237, 139, 76, 238, 101, 192)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__10 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__10_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__11 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__11_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__10_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__12 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__12_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__12_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__13 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__13_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__11_value),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__13_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__14 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__14_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "Std.Time.OffsetZ.hourMinuteSecondColon"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__15 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__15_value;
static lean_once_cell_t l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__16;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__17_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__17_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__2_value),LEAN_SCALAR_PTR_LITERAL(165, 154, 120, 218, 15, 36, 228, 254)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__17_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__35_value),LEAN_SCALAR_PTR_LITERAL(5, 26, 115, 31, 113, 82, 202, 87)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__17 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__17_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__17_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__18 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__18_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__17_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__19 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__19_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__19_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__20 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__20_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__18_value),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__20_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__21 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__21_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.G"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__0 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__0_value;
static lean_once_cell_t l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__1;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Modifier"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__2 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__2_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "G"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__3 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__3_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__4_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__4_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__4_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__3_value),LEAN_SCALAR_PTR_LITERAL(182, 140, 232, 180, 245, 222, 138, 191)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__4 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__4_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__5 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__5_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__4_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__6 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__6_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__7 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__7_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__5_value),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__7_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__8 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__8_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.u"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__9 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__9_value;
static lean_once_cell_t l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__10;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "u"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__11 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__11_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__12_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__12_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__12_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__11_value),LEAN_SCALAR_PTR_LITERAL(147, 80, 165, 32, 82, 240, 32, 222)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__12 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__12_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__12_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__13 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__13_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__12_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__14 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__14_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__14_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__15 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__15_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__13_value),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__15_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__16 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__16_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.y"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__17 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__17_value;
static lean_once_cell_t l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__18;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "y"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__19 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__19_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__20_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__20_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__20_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__19_value),LEAN_SCALAR_PTR_LITERAL(115, 95, 28, 131, 21, 96, 16, 178)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__20 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__20_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__20_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__21 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__21_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__20_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__22 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__22_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__22_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__23 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__23_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__21_value),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__23_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__24 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__24_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.D"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__25 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__25_value;
static lean_once_cell_t l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__26;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "D"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__27 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__27_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__28_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__28_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__28_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__28_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__28_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__27_value),LEAN_SCALAR_PTR_LITERAL(110, 212, 173, 37, 208, 12, 21, 131)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__28 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__28_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__28_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__29 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__29_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__28_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__30 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__30_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__30_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__31 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__31_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__29_value),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__31_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__32 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__32_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.M"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__33 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__33_value;
static lean_once_cell_t l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__34;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "M"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__35 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__35_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__36_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__36_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__36_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__36_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__36_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__36_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__35_value),LEAN_SCALAR_PTR_LITERAL(176, 179, 166, 105, 244, 184, 142, 60)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__36 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__36_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__36_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__37 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__37_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__36_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__38 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__38_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__38_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__39 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__39_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__37_value),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__39_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__40 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__40_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__41 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__41_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__42_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__42_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__42_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__42_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__42_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__42_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__41_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__42 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__42_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__43 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__43_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__44_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__44_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__44_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__44_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__44_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__44_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__43_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__44 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__44_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__45 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__45_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__46 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__46_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__46_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__47 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__47_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__48 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__48_value;
static lean_once_cell_t l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__49_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__49;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__50_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__50_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__50 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__50_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__50_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__51 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__51_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__52 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__52_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__52_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__53 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__53_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__54 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__54_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__55_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__55_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__55_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__55_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__54_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__55 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__55_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__55_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__56 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__56_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__57_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__57_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__57 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__57_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__57_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__58 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__58_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__59 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__59_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__59_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__60 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__60_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__60_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__61 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__61_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__58_value),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__61_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__62 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__62_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__56_value),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__62_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__63 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__63_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__53_value),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__63_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__64 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__64_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__51_value),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__64_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__65 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__65_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "dotIdent"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__66 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__66_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__67_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__67_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__67_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__67_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__67_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__67_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__66_value),LEAN_SCALAR_PTR_LITERAL(173, 139, 76, 218, 89, 59, 213, 196)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__67 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__67_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__68 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__68_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "inl"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__69 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__69_value;
static lean_once_cell_t l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__70_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__70;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__69_value),LEAN_SCALAR_PTR_LITERAL(86, 142, 99, 99, 156, 120, 56, 132)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__71 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__71_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__72 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__72_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "inr"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__73 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__73_value;
static lean_once_cell_t l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__74_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__74;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__73_value),LEAN_SCALAR_PTR_LITERAL(209, 212, 202, 104, 137, 8, 49, 108)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__75 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__75_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.L"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__76 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__76_value;
static lean_once_cell_t l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__77_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__77;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__78_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "L"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__78 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__78_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__79_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__79_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__79_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__79_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__79_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__79_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__78_value),LEAN_SCALAR_PTR_LITERAL(10, 49, 255, 3, 30, 59, 119, 162)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__79 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__79_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__80_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__79_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__80 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__80_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__81_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__79_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__81 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__81_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__82_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__81_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__82 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__82_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__83_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__80_value),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__82_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__83 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__83_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__84_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.d"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__84 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__84_value;
static lean_once_cell_t l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__85_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__85;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__86_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "d"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__86 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__86_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__87_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__87_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__87_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__87_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__87_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__87_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__87_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__86_value),LEAN_SCALAR_PTR_LITERAL(43, 177, 95, 132, 207, 75, 80, 59)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__87 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__87_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__88_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__87_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__88 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__88_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__89_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__87_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__89 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__89_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__90_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__89_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__90 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__90_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__91_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__88_value),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__90_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__91 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__91_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__92_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.Q"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__92 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__92_value;
static lean_once_cell_t l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__93_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__93;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__94_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "Q"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__94 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__94_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__95_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__95_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__95_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__95_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__95_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__95_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__95_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__94_value),LEAN_SCALAR_PTR_LITERAL(2, 45, 222, 148, 85, 12, 195, 87)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__95 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__95_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__96_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__95_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__96 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__96_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__97_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__95_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__97 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__97_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__98_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__97_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__98 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__98_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__99_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__96_value),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__98_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__99 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__99_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__100_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.q"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__100 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__100_value;
static lean_once_cell_t l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__101_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__101;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__102_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "q"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__102 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__102_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__103_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__103_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__103_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__103_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__103_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__103_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__103_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__102_value),LEAN_SCALAR_PTR_LITERAL(236, 248, 36, 9, 92, 215, 91, 102)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__103 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__103_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__104_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__103_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__104 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__104_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__105_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__103_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__105 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__105_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__106_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__105_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__106 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__106_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__107_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__104_value),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__106_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__107 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__107_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__108_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.Y"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__108 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__108_value;
static lean_once_cell_t l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__109_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__109;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__110_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "Y"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__110 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__110_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__111_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__111_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__111_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__111_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__111_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__111_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__111_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__110_value),LEAN_SCALAR_PTR_LITERAL(14, 155, 135, 75, 42, 253, 153, 241)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__111 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__111_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__112_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__111_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__112 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__112_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__113_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__111_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__113 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__113_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__114_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__113_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__114 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__114_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__115_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__112_value),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__114_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__115 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__115_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__116_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.w"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__116 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__116_value;
static lean_once_cell_t l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__117_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__117;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__118_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "w"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__118 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__118_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__119_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__119_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__119_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__119_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__119_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__119_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__119_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__118_value),LEAN_SCALAR_PTR_LITERAL(109, 122, 115, 3, 58, 174, 210, 61)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__119 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__119_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__120_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__119_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__120 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__120_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__121_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__119_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__121 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__121_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__122_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__121_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__122 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__122_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__123_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__120_value),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__122_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__123 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__123_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__124_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.W"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__124 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__124_value;
static lean_once_cell_t l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__125_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__125;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__126_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "W"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__126 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__126_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__127_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__127_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__127_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__127_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__127_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__127_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__127_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__126_value),LEAN_SCALAR_PTR_LITERAL(142, 210, 249, 219, 201, 68, 141, 242)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__127 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__127_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__128_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__127_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__128 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__128_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__129_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__127_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__129 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__129_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__130_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__129_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__130 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__130_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__131_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__128_value),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__130_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__131 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__131_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__132_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.E"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__132 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__132_value;
static lean_once_cell_t l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__133_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__133;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__134_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "E"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__134 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__134_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__135_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__135_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__135_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__135_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__135_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__135_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__135_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__134_value),LEAN_SCALAR_PTR_LITERAL(221, 114, 205, 107, 57, 101, 237, 55)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__135 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__135_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__136_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__135_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__136 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__136_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__137_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__135_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__137 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__137_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__138_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__137_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__138 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__138_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__139_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__136_value),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__138_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__139 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__139_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__140_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.e"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__140 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__140_value;
static lean_once_cell_t l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__141_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__141;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__142_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "e"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__142 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__142_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__143_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__143_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__143_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__143_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__143_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__143_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__143_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__142_value),LEAN_SCALAR_PTR_LITERAL(65, 97, 136, 164, 196, 185, 6, 236)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__143 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__143_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__144_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__143_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__144 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__144_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__145_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__143_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__145 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__145_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__146_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__145_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__146 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__146_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__147_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__144_value),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__146_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__147 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__147_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__148_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.c"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__148 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__148_value;
static lean_once_cell_t l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__149_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__149;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__150_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "c"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__150 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__150_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__151_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__151_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__151_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__151_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__151_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__151_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__151_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__150_value),LEAN_SCALAR_PTR_LITERAL(85, 172, 192, 170, 145, 101, 192, 197)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__151 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__151_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__152_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__151_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__152 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__152_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__153_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__151_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__153 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__153_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__154_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__153_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__154 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__154_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__155_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__152_value),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__154_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__155 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__155_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__156_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.F"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__156 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__156_value;
static lean_once_cell_t l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__157_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__157;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__158_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "F"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__158 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__158_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__159_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__159_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__159_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__159_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__159_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__159_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__159_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__158_value),LEAN_SCALAR_PTR_LITERAL(255, 172, 252, 76, 184, 53, 176, 25)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__159 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__159_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__160_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__159_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__160 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__160_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__161_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__159_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__161 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__161_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__162_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__161_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__162 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__162_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__163_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__160_value),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__162_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__163 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__163_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__164_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.a"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__164 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__164_value;
static lean_once_cell_t l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__165_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__165;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__166_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "a"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__166 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__166_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__167_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__167_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__167_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__167_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__167_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__167_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__167_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__166_value),LEAN_SCALAR_PTR_LITERAL(36, 69, 244, 234, 150, 73, 242, 198)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__167 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__167_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__168_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__167_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__168 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__168_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__169_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__167_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__169 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__169_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__170_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__169_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__170 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__170_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__171_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__168_value),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__170_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__171 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__171_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__172_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.b"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__172 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__172_value;
static lean_once_cell_t l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__173_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__173;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__174_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "b"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__174 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__174_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__175_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__175_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__175_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__175_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__175_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__175_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__175_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__174_value),LEAN_SCALAR_PTR_LITERAL(44, 133, 176, 52, 47, 30, 166, 26)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__175 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__175_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__176_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__175_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__176 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__176_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__177_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__175_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__177 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__177_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__178_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__177_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__178 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__178_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__179_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__176_value),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__178_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__179 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__179_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__180_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.B"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__180 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__180_value;
static lean_once_cell_t l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__181_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__181;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__182_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "B"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__182 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__182_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__183_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__183_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__183_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__183_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__183_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__183_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__183_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__182_value),LEAN_SCALAR_PTR_LITERAL(235, 206, 18, 37, 245, 139, 43, 135)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__183 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__183_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__184_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__183_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__184 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__184_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__185_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__183_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__185 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__185_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__186_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__185_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__186 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__186_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__187_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__184_value),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__186_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__187 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__187_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__188_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.h"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__188 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__188_value;
static lean_once_cell_t l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__189_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__189;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__190_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__190 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__190_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__191_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__191_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__191_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__191_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__191_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__191_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__191_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__190_value),LEAN_SCALAR_PTR_LITERAL(171, 19, 0, 95, 105, 8, 122, 135)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__191 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__191_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__192_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__191_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__192 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__192_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__193_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__191_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__193 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__193_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__194_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__193_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__194 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__194_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__195_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__192_value),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__194_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__195 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__195_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__196_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.K"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__196 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__196_value;
static lean_once_cell_t l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__197_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__197;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__198_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "K"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__198 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__198_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__199_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__199_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__199_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__199_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__199_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__199_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__199_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__198_value),LEAN_SCALAR_PTR_LITERAL(175, 237, 107, 230, 188, 207, 116, 239)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__199 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__199_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__200_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__199_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__200 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__200_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__201_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__199_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__201 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__201_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__202_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__201_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__202 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__202_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__203_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__200_value),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__202_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__203 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__203_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__204_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.k"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__204 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__204_value;
static lean_once_cell_t l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__205_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__205;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__206_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "k"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__206 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__206_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__207_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__207_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__207_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__207_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__207_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__207_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__207_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__206_value),LEAN_SCALAR_PTR_LITERAL(186, 55, 92, 94, 160, 8, 215, 223)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__207 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__207_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__208_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__207_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__208 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__208_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__209_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__207_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__209 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__209_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__210_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__209_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__210 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__210_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__211_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__208_value),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__210_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__211 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__211_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__212_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.H"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__212 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__212_value;
static lean_once_cell_t l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__213_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__213;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__214_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "H"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__214 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__214_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__215_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__215_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__215_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__215_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__215_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__215_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__215_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__214_value),LEAN_SCALAR_PTR_LITERAL(202, 31, 161, 0, 128, 16, 18, 169)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__215 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__215_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__216_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__215_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__216 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__216_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__217_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__215_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__217 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__217_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__218_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__217_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__218 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__218_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__219_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__216_value),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__218_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__219 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__219_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__220_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.m"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__220 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__220_value;
static lean_once_cell_t l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__221_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__221;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__222_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "m"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__222 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__222_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__223_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__223_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__223_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__223_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__223_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__223_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__223_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__222_value),LEAN_SCALAR_PTR_LITERAL(118, 254, 173, 99, 0, 222, 89, 33)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__223 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__223_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__224_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__223_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__224 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__224_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__225_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__223_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__225 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__225_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__226_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__225_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__226 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__226_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__227_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__224_value),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__226_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__227 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__227_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__228_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.s"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__228 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__228_value;
static lean_once_cell_t l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__229_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__229;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__230_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "s"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__230 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__230_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__231_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__231_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__231_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__231_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__231_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__231_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__231_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__230_value),LEAN_SCALAR_PTR_LITERAL(80, 170, 75, 145, 176, 122, 31, 111)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__231 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__231_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__232_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__231_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__232 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__232_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__233_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__231_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__233 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__233_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__234_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__233_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__234 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__234_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__235_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__232_value),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__234_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__235 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__235_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__236_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.S"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__236 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__236_value;
static lean_once_cell_t l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__237_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__237;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__238_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "S"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__238 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__238_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__239_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__239_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__239_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__239_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__239_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__239_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__239_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__238_value),LEAN_SCALAR_PTR_LITERAL(61, 110, 227, 5, 165, 49, 182, 207)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__239 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__239_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__240_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__239_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__240 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__240_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__241_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__239_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__241 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__241_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__242_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__241_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__242 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__242_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__243_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__240_value),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__242_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__243 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__243_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__244_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.A"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__244 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__244_value;
static lean_once_cell_t l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__245_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__245;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__246_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "A"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__246 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__246_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__247_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__247_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__247_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__247_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__247_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__247_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__247_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__246_value),LEAN_SCALAR_PTR_LITERAL(254, 42, 156, 100, 183, 179, 31, 180)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__247 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__247_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__248_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__247_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__248 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__248_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__249_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__247_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__249 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__249_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__250_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__249_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__250 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__250_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__251_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__248_value),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__250_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__251 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__251_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__252_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.n"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__252 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__252_value;
static lean_once_cell_t l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__253_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__253;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__254_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "n"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__254 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__254_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__255_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__255_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__255_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__255_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__255_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__255_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__255_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__254_value),LEAN_SCALAR_PTR_LITERAL(38, 78, 251, 143, 117, 169, 85, 233)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__255 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__255_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__256_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__255_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__256 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__256_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__257_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__255_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__257 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__257_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__258_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__257_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__258 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__258_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__259_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__256_value),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__258_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__259 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__259_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__260_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.N"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__260 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__260_value;
static lean_once_cell_t l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__261_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__261;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__262_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "N"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__262 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__262_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__263_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__263_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__263_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__263_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__263_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__263_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__263_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__262_value),LEAN_SCALAR_PTR_LITERAL(139, 9, 15, 62, 231, 211, 146, 60)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__263 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__263_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__264_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__263_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__264 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__264_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__265_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__263_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__265 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__265_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__266_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__265_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__266 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__266_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__267_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__264_value),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__266_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__267 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__267_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__268_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.V"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__268 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__268_value;
static lean_once_cell_t l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__269_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__269;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__270_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "V"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__270 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__270_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__271_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__271_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__271_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__271_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__271_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__271_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__271_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__270_value),LEAN_SCALAR_PTR_LITERAL(49, 190, 37, 135, 7, 5, 128, 4)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__271 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__271_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__272_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__271_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__272 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__272_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__273_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__271_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__273 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__273_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__274_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__273_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__274 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__274_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__275_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__272_value),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__274_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__275 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__275_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__276_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.z"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__276 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__276_value;
static lean_once_cell_t l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__277_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__277;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__278_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "z"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__278 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__278_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__279_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__279_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__279_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__279_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__279_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__279_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__279_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__278_value),LEAN_SCALAR_PTR_LITERAL(181, 218, 97, 100, 129, 163, 177, 227)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__279 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__279_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__280_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__279_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__280 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__280_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__281_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__279_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__281 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__281_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__282_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__281_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__282 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__282_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__283_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__280_value),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__282_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__283 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__283_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__284_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.v"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__284 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__284_value;
static lean_once_cell_t l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__285_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__285;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__286_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "v"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__286 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__286_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__287_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__287_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__287_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__287_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__287_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__287_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__287_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__286_value),LEAN_SCALAR_PTR_LITERAL(213, 204, 59, 153, 58, 232, 246, 39)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__287 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__287_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__288_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__287_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__288 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__288_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__289_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__287_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__289 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__289_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__290_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__289_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__290 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__290_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__291_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__288_value),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__290_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__291 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__291_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__292_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.O"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__292 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__292_value;
static lean_once_cell_t l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__293_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__293;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__294_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "O"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__294 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__294_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__295_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__295_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__295_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__295_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__295_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__295_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__295_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__294_value),LEAN_SCALAR_PTR_LITERAL(58, 151, 205, 45, 234, 213, 167, 33)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__295 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__295_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__296_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__295_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__296 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__296_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__297_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__295_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__297 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__297_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__298_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__297_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__298 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__298_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__299_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__296_value),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__298_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__299 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__299_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__300_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.X"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__300 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__300_value;
static lean_once_cell_t l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__301_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__301;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__302_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "X"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__302 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__302_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__303_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__303_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__303_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__303_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__303_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__303_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__303_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__302_value),LEAN_SCALAR_PTR_LITERAL(26, 41, 196, 142, 13, 161, 206, 121)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__303 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__303_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__304_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__303_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__304 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__304_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__305_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__303_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__305 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__305_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__306_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__305_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__306 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__306_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__307_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__304_value),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__306_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__307 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__307_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__308_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.x"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__308 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__308_value;
static lean_once_cell_t l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__309_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__309;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__310_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__310 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__310_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__311_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__311_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__311_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__311_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__311_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__311_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__311_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__310_value),LEAN_SCALAR_PTR_LITERAL(200, 2, 62, 177, 15, 17, 219, 69)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__311 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__311_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__312_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__311_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__312 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__312_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__313_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__311_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__313 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__313_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__314_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__313_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__314 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__314_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__315_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__312_value),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__314_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__315 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__315_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__316_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Time.Modifier.Z"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__316 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__316_value;
static lean_once_cell_t l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__317_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__317;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__318_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "Z"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__318 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__318_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__319_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__319_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__319_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__319_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__319_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 108, 36, 40, 30, 100, 55, 195)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__319_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__319_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__318_value),LEAN_SCALAR_PTR_LITERAL(44, 18, 171, 9, 22, 243, 82, 66)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__319 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__319_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__320_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__319_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__320 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__320_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__321_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__319_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__321 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__321_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__322_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__321_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__322 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__322_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__323_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__320_value),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__322_value)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__323 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__323_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertFormatPart___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "string"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertFormatPart___closed__0 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertFormatPart___closed__0_value;
static lean_once_cell_t l___private_Std_Time_Notation_Spec_0__Std_Time_convertFormatPart___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertFormatPart___closed__1;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertFormatPart___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertFormatPart___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 56, 52, 137, 138, 241, 128, 175)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertFormatPart___closed__2 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertFormatPart___closed__2_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertFormatPart___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "modifier"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertFormatPart___closed__3 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertFormatPart___closed__3_value;
static lean_once_cell_t l___private_Std_Time_Notation_Spec_0__Std_Time_convertFormatPart___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertFormatPart___closed__4;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_convertFormatPart___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertFormatPart___closed__3_value),LEAN_SCALAR_PTR_LITERAL(225, 238, 236, 22, 130, 68, 194, 201)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertFormatPart___closed__5 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertFormatPart___closed__5_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertFormatPart(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertFormatPart___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Time_termDatespec_x28___x29___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "termDatespec(_)"};
static const lean_object* l_Std_Time_termDatespec_x28___x29___closed__0 = (const lean_object*)&l_Std_Time_termDatespec_x28___x29___closed__0_value;
static const lean_ctor_object l_Std_Time_termDatespec_x28___x29___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Time_termDatespec_x28___x29___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_termDatespec_x28___x29___closed__1_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l_Std_Time_termDatespec_x28___x29___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_termDatespec_x28___x29___closed__1_value_aux_1),((lean_object*)&l_Std_Time_termDatespec_x28___x29___closed__0_value),LEAN_SCALAR_PTR_LITERAL(118, 128, 190, 137, 197, 98, 142, 204)}};
static const lean_object* l_Std_Time_termDatespec_x28___x29___closed__1 = (const lean_object*)&l_Std_Time_termDatespec_x28___x29___closed__1_value;
static const lean_string_object l_Std_Time_termDatespec_x28___x29___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Std_Time_termDatespec_x28___x29___closed__2 = (const lean_object*)&l_Std_Time_termDatespec_x28___x29___closed__2_value;
static const lean_ctor_object l_Std_Time_termDatespec_x28___x29___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_termDatespec_x28___x29___closed__2_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Std_Time_termDatespec_x28___x29___closed__3 = (const lean_object*)&l_Std_Time_termDatespec_x28___x29___closed__3_value;
static const lean_string_object l_Std_Time_termDatespec_x28___x29___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "datespec("};
static const lean_object* l_Std_Time_termDatespec_x28___x29___closed__4 = (const lean_object*)&l_Std_Time_termDatespec_x28___x29___closed__4_value;
static const lean_ctor_object l_Std_Time_termDatespec_x28___x29___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_termDatespec_x28___x29___closed__4_value)}};
static const lean_object* l_Std_Time_termDatespec_x28___x29___closed__5 = (const lean_object*)&l_Std_Time_termDatespec_x28___x29___closed__5_value;
static const lean_string_object l_Std_Time_termDatespec_x28___x29___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l_Std_Time_termDatespec_x28___x29___closed__6 = (const lean_object*)&l_Std_Time_termDatespec_x28___x29___closed__6_value;
static const lean_ctor_object l_Std_Time_termDatespec_x28___x29___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_termDatespec_x28___x29___closed__6_value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l_Std_Time_termDatespec_x28___x29___closed__7 = (const lean_object*)&l_Std_Time_termDatespec_x28___x29___closed__7_value;
static const lean_ctor_object l_Std_Time_termDatespec_x28___x29___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Time_termDatespec_x28___x29___closed__7_value)}};
static const lean_object* l_Std_Time_termDatespec_x28___x29___closed__8 = (const lean_object*)&l_Std_Time_termDatespec_x28___x29___closed__8_value;
static const lean_ctor_object l_Std_Time_termDatespec_x28___x29___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Time_termDatespec_x28___x29___closed__3_value),((lean_object*)&l_Std_Time_termDatespec_x28___x29___closed__5_value),((lean_object*)&l_Std_Time_termDatespec_x28___x29___closed__8_value)}};
static const lean_object* l_Std_Time_termDatespec_x28___x29___closed__9 = (const lean_object*)&l_Std_Time_termDatespec_x28___x29___closed__9_value;
static const lean_ctor_object l_Std_Time_termDatespec_x28___x29___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__72_value)}};
static const lean_object* l_Std_Time_termDatespec_x28___x29___closed__10 = (const lean_object*)&l_Std_Time_termDatespec_x28___x29___closed__10_value;
static const lean_ctor_object l_Std_Time_termDatespec_x28___x29___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Time_termDatespec_x28___x29___closed__3_value),((lean_object*)&l_Std_Time_termDatespec_x28___x29___closed__9_value),((lean_object*)&l_Std_Time_termDatespec_x28___x29___closed__10_value)}};
static const lean_object* l_Std_Time_termDatespec_x28___x29___closed__11 = (const lean_object*)&l_Std_Time_termDatespec_x28___x29___closed__11_value;
static const lean_ctor_object l_Std_Time_termDatespec_x28___x29___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_termDatespec_x28___x29___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Std_Time_termDatespec_x28___x29___closed__11_value)}};
static const lean_object* l_Std_Time_termDatespec_x28___x29___closed__12 = (const lean_object*)&l_Std_Time_termDatespec_x28___x29___closed__12_value;
LEAN_EXPORT const lean_object* l_Std_Time_termDatespec_x28___x29 = (const lean_object*)&l_Std_Time_termDatespec_x28___x29___closed__12_value;
static const lean_string_object l_Std_Time_termDatespec_x28___x2c___x29___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "termDatespec(_,_)"};
static const lean_object* l_Std_Time_termDatespec_x28___x2c___x29___closed__0 = (const lean_object*)&l_Std_Time_termDatespec_x28___x2c___x29___closed__0_value;
static const lean_ctor_object l_Std_Time_termDatespec_x28___x2c___x29___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Time_termDatespec_x28___x2c___x29___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_termDatespec_x28___x2c___x29___closed__1_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l_Std_Time_termDatespec_x28___x2c___x29___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_termDatespec_x28___x2c___x29___closed__1_value_aux_1),((lean_object*)&l_Std_Time_termDatespec_x28___x2c___x29___closed__0_value),LEAN_SCALAR_PTR_LITERAL(50, 74, 99, 46, 223, 91, 91, 115)}};
static const lean_object* l_Std_Time_termDatespec_x28___x2c___x29___closed__1 = (const lean_object*)&l_Std_Time_termDatespec_x28___x2c___x29___closed__1_value;
static const lean_string_object l_Std_Time_termDatespec_x28___x2c___x29___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Std_Time_termDatespec_x28___x2c___x29___closed__2 = (const lean_object*)&l_Std_Time_termDatespec_x28___x2c___x29___closed__2_value;
static const lean_ctor_object l_Std_Time_termDatespec_x28___x2c___x29___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_termDatespec_x28___x2c___x29___closed__2_value)}};
static const lean_object* l_Std_Time_termDatespec_x28___x2c___x29___closed__3 = (const lean_object*)&l_Std_Time_termDatespec_x28___x2c___x29___closed__3_value;
static const lean_ctor_object l_Std_Time_termDatespec_x28___x2c___x29___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Time_termDatespec_x28___x29___closed__3_value),((lean_object*)&l_Std_Time_termDatespec_x28___x29___closed__9_value),((lean_object*)&l_Std_Time_termDatespec_x28___x2c___x29___closed__3_value)}};
static const lean_object* l_Std_Time_termDatespec_x28___x2c___x29___closed__4 = (const lean_object*)&l_Std_Time_termDatespec_x28___x2c___x29___closed__4_value;
static const lean_string_object l_Std_Time_termDatespec_x28___x2c___x29___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Std_Time_termDatespec_x28___x2c___x29___closed__5 = (const lean_object*)&l_Std_Time_termDatespec_x28___x2c___x29___closed__5_value;
static const lean_ctor_object l_Std_Time_termDatespec_x28___x2c___x29___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_termDatespec_x28___x2c___x29___closed__5_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Std_Time_termDatespec_x28___x2c___x29___closed__6 = (const lean_object*)&l_Std_Time_termDatespec_x28___x2c___x29___closed__6_value;
static const lean_ctor_object l_Std_Time_termDatespec_x28___x2c___x29___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Std_Time_termDatespec_x28___x2c___x29___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Time_termDatespec_x28___x2c___x29___closed__7 = (const lean_object*)&l_Std_Time_termDatespec_x28___x2c___x29___closed__7_value;
static const lean_ctor_object l_Std_Time_termDatespec_x28___x2c___x29___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Time_termDatespec_x28___x29___closed__3_value),((lean_object*)&l_Std_Time_termDatespec_x28___x2c___x29___closed__4_value),((lean_object*)&l_Std_Time_termDatespec_x28___x2c___x29___closed__7_value)}};
static const lean_object* l_Std_Time_termDatespec_x28___x2c___x29___closed__8 = (const lean_object*)&l_Std_Time_termDatespec_x28___x2c___x29___closed__8_value;
static const lean_ctor_object l_Std_Time_termDatespec_x28___x2c___x29___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Time_termDatespec_x28___x29___closed__3_value),((lean_object*)&l_Std_Time_termDatespec_x28___x2c___x29___closed__8_value),((lean_object*)&l_Std_Time_termDatespec_x28___x29___closed__10_value)}};
static const lean_object* l_Std_Time_termDatespec_x28___x2c___x29___closed__9 = (const lean_object*)&l_Std_Time_termDatespec_x28___x2c___x29___closed__9_value;
static const lean_ctor_object l_Std_Time_termDatespec_x28___x2c___x29___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_termDatespec_x28___x2c___x29___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Std_Time_termDatespec_x28___x2c___x29___closed__9_value)}};
static const lean_object* l_Std_Time_termDatespec_x28___x2c___x29___closed__10 = (const lean_object*)&l_Std_Time_termDatespec_x28___x2c___x29___closed__10_value;
LEAN_EXPORT const lean_object* l_Std_Time_termDatespec_x28___x2c___x29 = (const lean_object*)&l_Std_Time_termDatespec_x28___x2c___x29___closed__10_value;
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__0;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "cannot compile spec: "};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__1 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__1_value;
static const lean_array_object l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__2 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__2_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "anonymousCtor"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__3 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__3_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__4_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__4_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__4_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__3_value),LEAN_SCALAR_PTR_LITERAL(56, 53, 154, 97, 179, 232, 94, 186)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__4 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__4_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟨"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__5 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__5_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "term[_]"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__6 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__6_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__6_value),LEAN_SCALAR_PTR_LITERAL(86, 147, 168, 74, 195, 98, 232, 161)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__7 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__7_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__8 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__8_value;
static lean_once_cell_t l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__9;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__10 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__10_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟩"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__11 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__11_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "term{}"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__12 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__12_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__12_value),LEAN_SCALAR_PTR_LITERAL(44, 141, 217, 101, 193, 131, 35, 71)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__13 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__13_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "{"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__14 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__14_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__15 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__15_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "structInst"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__16 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__16_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__17_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__17_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__17_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__16_value),LEAN_SCALAR_PTR_LITERAL(50, 43, 73, 62, 118, 124, 31, 28)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__17 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__17_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "structInstFields"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__18 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__18_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__19_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__19_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__19_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__18_value),LEAN_SCALAR_PTR_LITERAL(0, 82, 141, 43, 62, 171, 163, 69)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__19 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__19_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "optEllipsis"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__20 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__20_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__21_value_aux_0),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__21_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__21_value_aux_1),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__21_value_aux_2),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__20_value),LEAN_SCALAR_PTR_LITERAL(13, 1, 242, 203, 207, 188, 181, 160)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__21 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__21_value;
static const lean_string_object l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "choice"};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__22 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__22_value;
static const lean_ctor_object l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__22_value),LEAN_SCALAR_PTR_LITERAL(59, 66, 148, 42, 181, 100, 85, 166)}};
static const lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__23 = (const lean_object*)&l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__23_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time___aux__Std__Time__Notation__Spec______macroRules__Std__Time__termDatespec_x28___x29__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time___aux__Std__Time__Notation__Spec______macroRules__Std__Time__termDatespec_x28___x29__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time___aux__Std__Time__Notation__Spec______macroRules__Std__Time__termDatespec_x28___x2c___x29__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time___aux__Std__Time__Notation__Spec______macroRules__Std__Time__termDatespec_x28___x2c___x29__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__1(void){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__0));
v___x_3_ = l_String_toRawSubstring_x27(v___x_2_);
return v___x_3_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__12(void){
_start:
{
lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_25_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__11));
v___x_26_ = l_String_toRawSubstring_x27(v___x_25_);
return v___x_26_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__20(void){
_start:
{
lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_45_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__19));
v___x_46_ = l_String_toRawSubstring_x27(v___x_45_);
return v___x_46_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__28(void){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_65_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__27));
v___x_66_ = l_String_toRawSubstring_x27(v___x_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertText(uint8_t v_x_84_, lean_object* v_a_85_, lean_object* v_a_86_){
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
v___x_92_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__1, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__1_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__1);
v___x_93_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__6));
lean_inc(v_currMacroScope_88_);
lean_inc(v_quotContext_87_);
v___x_94_ = l_Lean_addMacroScope(v_quotContext_87_, v___x_93_, v_currMacroScope_88_);
v___x_95_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__10));
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
v___x_103_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__12, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__12_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__12);
v___x_104_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__14));
lean_inc(v_currMacroScope_99_);
lean_inc(v_quotContext_98_);
v___x_105_ = l_Lean_addMacroScope(v_quotContext_98_, v___x_104_, v_currMacroScope_99_);
v___x_106_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__18));
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
v___x_114_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__20, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__20_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__20);
v___x_115_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__22));
lean_inc(v_currMacroScope_110_);
lean_inc(v_quotContext_109_);
v___x_116_ = l_Lean_addMacroScope(v_quotContext_109_, v___x_115_, v_currMacroScope_110_);
v___x_117_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__26));
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
v___x_125_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__28, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__28_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__28);
v___x_126_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__30));
lean_inc(v_currMacroScope_121_);
lean_inc(v_quotContext_120_);
v___x_127_ = l_Lean_addMacroScope(v_quotContext_120_, v___x_126_, v_currMacroScope_121_);
v___x_128_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__34));
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
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___boxed(lean_object* v_x_131_, lean_object* v_a_132_, lean_object* v_a_133_){
_start:
{
uint8_t v_x_5371__boxed_134_; lean_object* v_res_135_; 
v_x_5371__boxed_134_ = lean_unbox(v_x_131_);
v_res_135_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertText(v_x_5371__boxed_134_, v_a_132_, v_a_133_);
lean_dec_ref(v_a_132_);
return v_res_135_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__6(void){
_start:
{
lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_146_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__5));
v___x_147_ = l_String_toRawSubstring_x27(v___x_146_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber(lean_object* v_x_169_, lean_object* v_a_170_, lean_object* v_a_171_){
_start:
{
lean_object* v_quotContext_172_; lean_object* v_currMacroScope_173_; lean_object* v_ref_174_; uint8_t v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
v_quotContext_172_ = lean_ctor_get(v_a_170_, 1);
v_currMacroScope_173_ = lean_ctor_get(v_a_170_, 2);
v_ref_174_ = lean_ctor_get(v_a_170_, 5);
v___x_175_ = 0;
v___x_176_ = l_Lean_SourceInfo_fromRef(v_ref_174_, v___x_175_);
v___x_177_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4));
v___x_178_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__6, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__6_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__6);
v___x_179_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__9));
lean_inc(v_currMacroScope_173_);
lean_inc(v_quotContext_172_);
v___x_180_ = l_Lean_addMacroScope(v_quotContext_172_, v___x_179_, v_currMacroScope_173_);
v___x_181_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__13));
lean_inc_n(v___x_176_, 2);
v___x_182_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_182_, 0, v___x_176_);
lean_ctor_set(v___x_182_, 1, v___x_178_);
lean_ctor_set(v___x_182_, 2, v___x_180_);
lean_ctor_set(v___x_182_, 3, v___x_181_);
v___x_183_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15));
v___x_184_ = l_Nat_reprFast(v_x_169_);
v___x_185_ = lean_box(2);
v___x_186_ = l_Lean_Syntax_mkNumLit(v___x_184_, v___x_185_);
v___x_187_ = l_Lean_Syntax_node1(v___x_176_, v___x_183_, v___x_186_);
v___x_188_ = l_Lean_Syntax_node2(v___x_176_, v___x_177_, v___x_182_, v___x_187_);
v___x_189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_189_, 0, v___x_188_);
lean_ctor_set(v___x_189_, 1, v_a_171_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___boxed(lean_object* v_x_190_, lean_object* v_a_191_, lean_object* v_a_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber(v_x_190_, v_a_191_, v_a_192_);
lean_dec_ref(v_a_191_);
return v_res_193_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__1(void){
_start:
{
lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_195_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__0));
v___x_196_ = l_String_toRawSubstring_x27(v___x_195_);
return v___x_196_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__10(void){
_start:
{
lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_216_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__9));
v___x_217_ = l_String_toRawSubstring_x27(v___x_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction(lean_object* v_x_235_, lean_object* v_a_236_, lean_object* v_a_237_){
_start:
{
if (lean_obj_tag(v_x_235_) == 0)
{
lean_object* v_quotContext_238_; lean_object* v_currMacroScope_239_; lean_object* v_ref_240_; uint8_t v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v_quotContext_238_ = lean_ctor_get(v_a_236_, 1);
v_currMacroScope_239_ = lean_ctor_get(v_a_236_, 2);
v_ref_240_ = lean_ctor_get(v_a_236_, 5);
v___x_241_ = 0;
v___x_242_ = l_Lean_SourceInfo_fromRef(v_ref_240_, v___x_241_);
v___x_243_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__1, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__1_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__1);
v___x_244_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__4));
lean_inc(v_currMacroScope_239_);
lean_inc(v_quotContext_238_);
v___x_245_ = l_Lean_addMacroScope(v_quotContext_238_, v___x_244_, v_currMacroScope_239_);
v___x_246_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__8));
v___x_247_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_247_, 0, v___x_242_);
lean_ctor_set(v___x_247_, 1, v___x_243_);
lean_ctor_set(v___x_247_, 2, v___x_245_);
lean_ctor_set(v___x_247_, 3, v___x_246_);
v___x_248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_248_, 0, v___x_247_);
lean_ctor_set(v___x_248_, 1, v_a_237_);
return v___x_248_;
}
else
{
lean_object* v_digits_249_; lean_object* v_quotContext_250_; lean_object* v_currMacroScope_251_; lean_object* v_ref_252_; uint8_t v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v_digits_249_ = lean_ctor_get(v_x_235_, 0);
lean_inc(v_digits_249_);
lean_dec_ref_known(v_x_235_, 1);
v_quotContext_250_ = lean_ctor_get(v_a_236_, 1);
v_currMacroScope_251_ = lean_ctor_get(v_a_236_, 2);
v_ref_252_ = lean_ctor_get(v_a_236_, 5);
v___x_253_ = 0;
v___x_254_ = l_Lean_SourceInfo_fromRef(v_ref_252_, v___x_253_);
v___x_255_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4));
v___x_256_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__10, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__10_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__10);
v___x_257_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__12));
lean_inc(v_currMacroScope_251_);
lean_inc(v_quotContext_250_);
v___x_258_ = l_Lean_addMacroScope(v_quotContext_250_, v___x_257_, v_currMacroScope_251_);
v___x_259_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__16));
lean_inc_n(v___x_254_, 2);
v___x_260_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_260_, 0, v___x_254_);
lean_ctor_set(v___x_260_, 1, v___x_256_);
lean_ctor_set(v___x_260_, 2, v___x_258_);
lean_ctor_set(v___x_260_, 3, v___x_259_);
v___x_261_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15));
v___x_262_ = l_Nat_reprFast(v_digits_249_);
v___x_263_ = lean_box(2);
v___x_264_ = l_Lean_Syntax_mkNumLit(v___x_262_, v___x_263_);
v___x_265_ = l_Lean_Syntax_node1(v___x_254_, v___x_261_, v___x_264_);
v___x_266_ = l_Lean_Syntax_node2(v___x_254_, v___x_255_, v___x_260_, v___x_265_);
v___x_267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_267_, 0, v___x_266_);
lean_ctor_set(v___x_267_, 1, v_a_237_);
return v___x_267_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___boxed(lean_object* v_x_268_, lean_object* v_a_269_, lean_object* v_a_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction(v_x_268_, v_a_269_, v_a_270_);
lean_dec_ref(v_a_269_);
return v_res_271_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__1(void){
_start:
{
lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_273_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__0));
v___x_274_ = l_String_toRawSubstring_x27(v___x_273_);
return v___x_274_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__10(void){
_start:
{
lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_294_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__9));
v___x_295_ = l_String_toRawSubstring_x27(v___x_294_);
return v___x_295_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__18(void){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_314_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__17));
v___x_315_ = l_String_toRawSubstring_x27(v___x_314_);
return v___x_315_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__26(void){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_334_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__25));
v___x_335_ = l_String_toRawSubstring_x27(v___x_334_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear(lean_object* v_x_353_, lean_object* v_a_354_, lean_object* v_a_355_){
_start:
{
switch(lean_obj_tag(v_x_353_))
{
case 0:
{
lean_object* v_quotContext_356_; lean_object* v_currMacroScope_357_; lean_object* v_ref_358_; uint8_t v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; 
v_quotContext_356_ = lean_ctor_get(v_a_354_, 1);
v_currMacroScope_357_ = lean_ctor_get(v_a_354_, 2);
v_ref_358_ = lean_ctor_get(v_a_354_, 5);
v___x_359_ = 0;
v___x_360_ = l_Lean_SourceInfo_fromRef(v_ref_358_, v___x_359_);
v___x_361_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__1, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__1_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__1);
v___x_362_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__4));
lean_inc(v_currMacroScope_357_);
lean_inc(v_quotContext_356_);
v___x_363_ = l_Lean_addMacroScope(v_quotContext_356_, v___x_362_, v_currMacroScope_357_);
v___x_364_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__8));
v___x_365_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_365_, 0, v___x_360_);
lean_ctor_set(v___x_365_, 1, v___x_361_);
lean_ctor_set(v___x_365_, 2, v___x_363_);
lean_ctor_set(v___x_365_, 3, v___x_364_);
v___x_366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_366_, 0, v___x_365_);
lean_ctor_set(v___x_366_, 1, v_a_355_);
return v___x_366_;
}
case 1:
{
lean_object* v_quotContext_367_; lean_object* v_currMacroScope_368_; lean_object* v_ref_369_; uint8_t v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; 
v_quotContext_367_ = lean_ctor_get(v_a_354_, 1);
v_currMacroScope_368_ = lean_ctor_get(v_a_354_, 2);
v_ref_369_ = lean_ctor_get(v_a_354_, 5);
v___x_370_ = 0;
v___x_371_ = l_Lean_SourceInfo_fromRef(v_ref_369_, v___x_370_);
v___x_372_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__10, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__10_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__10);
v___x_373_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__12));
lean_inc(v_currMacroScope_368_);
lean_inc(v_quotContext_367_);
v___x_374_ = l_Lean_addMacroScope(v_quotContext_367_, v___x_373_, v_currMacroScope_368_);
v___x_375_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__16));
v___x_376_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_376_, 0, v___x_371_);
lean_ctor_set(v___x_376_, 1, v___x_372_);
lean_ctor_set(v___x_376_, 2, v___x_374_);
lean_ctor_set(v___x_376_, 3, v___x_375_);
v___x_377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_377_, 0, v___x_376_);
lean_ctor_set(v___x_377_, 1, v_a_355_);
return v___x_377_;
}
case 2:
{
lean_object* v_quotContext_378_; lean_object* v_currMacroScope_379_; lean_object* v_ref_380_; uint8_t v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
v_quotContext_378_ = lean_ctor_get(v_a_354_, 1);
v_currMacroScope_379_ = lean_ctor_get(v_a_354_, 2);
v_ref_380_ = lean_ctor_get(v_a_354_, 5);
v___x_381_ = 0;
v___x_382_ = l_Lean_SourceInfo_fromRef(v_ref_380_, v___x_381_);
v___x_383_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__18, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__18_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__18);
v___x_384_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__20));
lean_inc(v_currMacroScope_379_);
lean_inc(v_quotContext_378_);
v___x_385_ = l_Lean_addMacroScope(v_quotContext_378_, v___x_384_, v_currMacroScope_379_);
v___x_386_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__24));
v___x_387_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_387_, 0, v___x_382_);
lean_ctor_set(v___x_387_, 1, v___x_383_);
lean_ctor_set(v___x_387_, 2, v___x_385_);
lean_ctor_set(v___x_387_, 3, v___x_386_);
v___x_388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_388_, 0, v___x_387_);
lean_ctor_set(v___x_388_, 1, v_a_355_);
return v___x_388_;
}
default: 
{
lean_object* v_num_389_; lean_object* v_quotContext_390_; lean_object* v_currMacroScope_391_; lean_object* v_ref_392_; uint8_t v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v_num_389_ = lean_ctor_get(v_x_353_, 0);
lean_inc(v_num_389_);
lean_dec_ref_known(v_x_353_, 1);
v_quotContext_390_ = lean_ctor_get(v_a_354_, 1);
v_currMacroScope_391_ = lean_ctor_get(v_a_354_, 2);
v_ref_392_ = lean_ctor_get(v_a_354_, 5);
v___x_393_ = 0;
v___x_394_ = l_Lean_SourceInfo_fromRef(v_ref_392_, v___x_393_);
v___x_395_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4));
v___x_396_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__26, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__26_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__26);
v___x_397_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__28));
lean_inc(v_currMacroScope_391_);
lean_inc(v_quotContext_390_);
v___x_398_ = l_Lean_addMacroScope(v_quotContext_390_, v___x_397_, v_currMacroScope_391_);
v___x_399_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__32));
lean_inc_n(v___x_394_, 2);
v___x_400_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_400_, 0, v___x_394_);
lean_ctor_set(v___x_400_, 1, v___x_396_);
lean_ctor_set(v___x_400_, 2, v___x_398_);
lean_ctor_set(v___x_400_, 3, v___x_399_);
v___x_401_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15));
v___x_402_ = l_Nat_reprFast(v_num_389_);
v___x_403_ = lean_box(2);
v___x_404_ = l_Lean_Syntax_mkNumLit(v___x_402_, v___x_403_);
v___x_405_ = l_Lean_Syntax_node1(v___x_394_, v___x_401_, v___x_404_);
v___x_406_ = l_Lean_Syntax_node2(v___x_394_, v___x_395_, v___x_400_, v___x_405_);
v___x_407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_407_, 0, v___x_406_);
lean_ctor_set(v___x_407_, 1, v_a_355_);
return v___x_407_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___boxed(lean_object* v_x_408_, lean_object* v_a_409_, lean_object* v_a_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear(v_x_408_, v_a_409_, v_a_410_);
lean_dec_ref(v_a_409_);
return v_res_411_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__1(void){
_start:
{
lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_413_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__0));
v___x_414_ = l_String_toRawSubstring_x27(v___x_413_);
return v___x_414_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__10(void){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_434_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__9));
v___x_435_ = l_String_toRawSubstring_x27(v___x_434_);
return v___x_435_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__17(void){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_453_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__16));
v___x_454_ = l_String_toRawSubstring_x27(v___x_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId(uint8_t v_x_471_, lean_object* v_a_472_, lean_object* v_a_473_){
_start:
{
switch(v_x_471_)
{
case 0:
{
lean_object* v_quotContext_474_; lean_object* v_currMacroScope_475_; lean_object* v_ref_476_; uint8_t v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v_quotContext_474_ = lean_ctor_get(v_a_472_, 1);
v_currMacroScope_475_ = lean_ctor_get(v_a_472_, 2);
v_ref_476_ = lean_ctor_get(v_a_472_, 5);
v___x_477_ = 0;
v___x_478_ = l_Lean_SourceInfo_fromRef(v_ref_476_, v___x_477_);
v___x_479_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__1, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__1_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__1);
v___x_480_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__4));
lean_inc(v_currMacroScope_475_);
lean_inc(v_quotContext_474_);
v___x_481_ = l_Lean_addMacroScope(v_quotContext_474_, v___x_480_, v_currMacroScope_475_);
v___x_482_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__8));
v___x_483_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_483_, 0, v___x_478_);
lean_ctor_set(v___x_483_, 1, v___x_479_);
lean_ctor_set(v___x_483_, 2, v___x_481_);
lean_ctor_set(v___x_483_, 3, v___x_482_);
v___x_484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_484_, 0, v___x_483_);
lean_ctor_set(v___x_484_, 1, v_a_473_);
return v___x_484_;
}
case 1:
{
lean_object* v_quotContext_485_; lean_object* v_currMacroScope_486_; lean_object* v_ref_487_; uint8_t v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v_quotContext_485_ = lean_ctor_get(v_a_472_, 1);
v_currMacroScope_486_ = lean_ctor_get(v_a_472_, 2);
v_ref_487_ = lean_ctor_get(v_a_472_, 5);
v___x_488_ = 0;
v___x_489_ = l_Lean_SourceInfo_fromRef(v_ref_487_, v___x_488_);
v___x_490_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__10, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__10_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__10);
v___x_491_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__11));
lean_inc(v_currMacroScope_486_);
lean_inc(v_quotContext_485_);
v___x_492_ = l_Lean_addMacroScope(v_quotContext_485_, v___x_491_, v_currMacroScope_486_);
v___x_493_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__15));
v___x_494_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_494_, 0, v___x_489_);
lean_ctor_set(v___x_494_, 1, v___x_490_);
lean_ctor_set(v___x_494_, 2, v___x_492_);
lean_ctor_set(v___x_494_, 3, v___x_493_);
v___x_495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_495_, 0, v___x_494_);
lean_ctor_set(v___x_495_, 1, v_a_473_);
return v___x_495_;
}
default: 
{
lean_object* v_quotContext_496_; lean_object* v_currMacroScope_497_; lean_object* v_ref_498_; uint8_t v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
v_quotContext_496_ = lean_ctor_get(v_a_472_, 1);
v_currMacroScope_497_ = lean_ctor_get(v_a_472_, 2);
v_ref_498_ = lean_ctor_get(v_a_472_, 5);
v___x_499_ = 0;
v___x_500_ = l_Lean_SourceInfo_fromRef(v_ref_498_, v___x_499_);
v___x_501_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__17, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__17_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__17);
v___x_502_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__18));
lean_inc(v_currMacroScope_497_);
lean_inc(v_quotContext_496_);
v___x_503_ = l_Lean_addMacroScope(v_quotContext_496_, v___x_502_, v_currMacroScope_497_);
v___x_504_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___closed__22));
v___x_505_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_505_, 0, v___x_500_);
lean_ctor_set(v___x_505_, 1, v___x_501_);
lean_ctor_set(v___x_505_, 2, v___x_503_);
lean_ctor_set(v___x_505_, 3, v___x_504_);
v___x_506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_506_, 0, v___x_505_);
lean_ctor_set(v___x_506_, 1, v_a_473_);
return v___x_506_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId___boxed(lean_object* v_x_507_, lean_object* v_a_508_, lean_object* v_a_509_){
_start:
{
uint8_t v_x_4028__boxed_510_; lean_object* v_res_511_; 
v_x_4028__boxed_510_ = lean_unbox(v_x_507_);
v_res_511_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId(v_x_4028__boxed_510_, v_a_508_, v_a_509_);
lean_dec_ref(v_a_508_);
return v_res_511_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__1(void){
_start:
{
lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_513_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__0));
v___x_514_ = l_String_toRawSubstring_x27(v___x_513_);
return v___x_514_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__9(void){
_start:
{
lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_533_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__8));
v___x_534_ = l_String_toRawSubstring_x27(v___x_533_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName(uint8_t v_x_551_, lean_object* v_a_552_, lean_object* v_a_553_){
_start:
{
if (v_x_551_ == 0)
{
lean_object* v_quotContext_554_; lean_object* v_currMacroScope_555_; lean_object* v_ref_556_; uint8_t v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
v_quotContext_554_ = lean_ctor_get(v_a_552_, 1);
v_currMacroScope_555_ = lean_ctor_get(v_a_552_, 2);
v_ref_556_ = lean_ctor_get(v_a_552_, 5);
v___x_557_ = 0;
v___x_558_ = l_Lean_SourceInfo_fromRef(v_ref_556_, v___x_557_);
v___x_559_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__1, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__1_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__1);
v___x_560_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__3));
lean_inc(v_currMacroScope_555_);
lean_inc(v_quotContext_554_);
v___x_561_ = l_Lean_addMacroScope(v_quotContext_554_, v___x_560_, v_currMacroScope_555_);
v___x_562_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__7));
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
else
{
lean_object* v_quotContext_565_; lean_object* v_currMacroScope_566_; lean_object* v_ref_567_; uint8_t v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v_quotContext_565_ = lean_ctor_get(v_a_552_, 1);
v_currMacroScope_566_ = lean_ctor_get(v_a_552_, 2);
v_ref_567_ = lean_ctor_get(v_a_552_, 5);
v___x_568_ = 0;
v___x_569_ = l_Lean_SourceInfo_fromRef(v_ref_567_, v___x_568_);
v___x_570_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__9, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__9_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__9);
v___x_571_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__10));
lean_inc(v_currMacroScope_566_);
lean_inc(v_quotContext_565_);
v___x_572_ = l_Lean_addMacroScope(v_quotContext_565_, v___x_571_, v_currMacroScope_566_);
v___x_573_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__14));
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
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___boxed(lean_object* v_x_576_, lean_object* v_a_577_, lean_object* v_a_578_){
_start:
{
uint8_t v_x_2689__boxed_579_; lean_object* v_res_580_; 
v_x_2689__boxed_579_ = lean_unbox(v_x_576_);
v_res_580_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName(v_x_2689__boxed_579_, v_a_577_, v_a_578_);
lean_dec_ref(v_a_577_);
return v_res_580_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__1(void){
_start:
{
lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_582_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__0));
v___x_583_ = l_String_toRawSubstring_x27(v___x_582_);
return v___x_583_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__10(void){
_start:
{
lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_603_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__9));
v___x_604_ = l_String_toRawSubstring_x27(v___x_603_);
return v___x_604_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__18(void){
_start:
{
lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_623_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__17));
v___x_624_ = l_String_toRawSubstring_x27(v___x_623_);
return v___x_624_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__26(void){
_start:
{
lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_643_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__25));
v___x_644_ = l_String_toRawSubstring_x27(v___x_643_);
return v___x_644_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__34(void){
_start:
{
lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_663_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__33));
v___x_664_ = l_String_toRawSubstring_x27(v___x_663_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX(uint8_t v_x_682_, lean_object* v_a_683_, lean_object* v_a_684_){
_start:
{
switch(v_x_682_)
{
case 0:
{
lean_object* v_quotContext_685_; lean_object* v_currMacroScope_686_; lean_object* v_ref_687_; uint8_t v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; 
v_quotContext_685_ = lean_ctor_get(v_a_683_, 1);
v_currMacroScope_686_ = lean_ctor_get(v_a_683_, 2);
v_ref_687_ = lean_ctor_get(v_a_683_, 5);
v___x_688_ = 0;
v___x_689_ = l_Lean_SourceInfo_fromRef(v_ref_687_, v___x_688_);
v___x_690_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__1, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__1_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__1);
v___x_691_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__4));
lean_inc(v_currMacroScope_686_);
lean_inc(v_quotContext_685_);
v___x_692_ = l_Lean_addMacroScope(v_quotContext_685_, v___x_691_, v_currMacroScope_686_);
v___x_693_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__8));
v___x_694_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_694_, 0, v___x_689_);
lean_ctor_set(v___x_694_, 1, v___x_690_);
lean_ctor_set(v___x_694_, 2, v___x_692_);
lean_ctor_set(v___x_694_, 3, v___x_693_);
v___x_695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_695_, 0, v___x_694_);
lean_ctor_set(v___x_695_, 1, v_a_684_);
return v___x_695_;
}
case 1:
{
lean_object* v_quotContext_696_; lean_object* v_currMacroScope_697_; lean_object* v_ref_698_; uint8_t v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v_quotContext_696_ = lean_ctor_get(v_a_683_, 1);
v_currMacroScope_697_ = lean_ctor_get(v_a_683_, 2);
v_ref_698_ = lean_ctor_get(v_a_683_, 5);
v___x_699_ = 0;
v___x_700_ = l_Lean_SourceInfo_fromRef(v_ref_698_, v___x_699_);
v___x_701_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__10, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__10_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__10);
v___x_702_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__12));
lean_inc(v_currMacroScope_697_);
lean_inc(v_quotContext_696_);
v___x_703_ = l_Lean_addMacroScope(v_quotContext_696_, v___x_702_, v_currMacroScope_697_);
v___x_704_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__16));
v___x_705_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_705_, 0, v___x_700_);
lean_ctor_set(v___x_705_, 1, v___x_701_);
lean_ctor_set(v___x_705_, 2, v___x_703_);
lean_ctor_set(v___x_705_, 3, v___x_704_);
v___x_706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_706_, 0, v___x_705_);
lean_ctor_set(v___x_706_, 1, v_a_684_);
return v___x_706_;
}
case 2:
{
lean_object* v_quotContext_707_; lean_object* v_currMacroScope_708_; lean_object* v_ref_709_; uint8_t v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
v_quotContext_707_ = lean_ctor_get(v_a_683_, 1);
v_currMacroScope_708_ = lean_ctor_get(v_a_683_, 2);
v_ref_709_ = lean_ctor_get(v_a_683_, 5);
v___x_710_ = 0;
v___x_711_ = l_Lean_SourceInfo_fromRef(v_ref_709_, v___x_710_);
v___x_712_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__18, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__18_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__18);
v___x_713_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__20));
lean_inc(v_currMacroScope_708_);
lean_inc(v_quotContext_707_);
v___x_714_ = l_Lean_addMacroScope(v_quotContext_707_, v___x_713_, v_currMacroScope_708_);
v___x_715_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__24));
v___x_716_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_716_, 0, v___x_711_);
lean_ctor_set(v___x_716_, 1, v___x_712_);
lean_ctor_set(v___x_716_, 2, v___x_714_);
lean_ctor_set(v___x_716_, 3, v___x_715_);
v___x_717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_717_, 0, v___x_716_);
lean_ctor_set(v___x_717_, 1, v_a_684_);
return v___x_717_;
}
case 3:
{
lean_object* v_quotContext_718_; lean_object* v_currMacroScope_719_; lean_object* v_ref_720_; uint8_t v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; 
v_quotContext_718_ = lean_ctor_get(v_a_683_, 1);
v_currMacroScope_719_ = lean_ctor_get(v_a_683_, 2);
v_ref_720_ = lean_ctor_get(v_a_683_, 5);
v___x_721_ = 0;
v___x_722_ = l_Lean_SourceInfo_fromRef(v_ref_720_, v___x_721_);
v___x_723_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__26, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__26_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__26);
v___x_724_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__28));
lean_inc(v_currMacroScope_719_);
lean_inc(v_quotContext_718_);
v___x_725_ = l_Lean_addMacroScope(v_quotContext_718_, v___x_724_, v_currMacroScope_719_);
v___x_726_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__32));
v___x_727_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_727_, 0, v___x_722_);
lean_ctor_set(v___x_727_, 1, v___x_723_);
lean_ctor_set(v___x_727_, 2, v___x_725_);
lean_ctor_set(v___x_727_, 3, v___x_726_);
v___x_728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_728_, 0, v___x_727_);
lean_ctor_set(v___x_728_, 1, v_a_684_);
return v___x_728_;
}
default: 
{
lean_object* v_quotContext_729_; lean_object* v_currMacroScope_730_; lean_object* v_ref_731_; uint8_t v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; 
v_quotContext_729_ = lean_ctor_get(v_a_683_, 1);
v_currMacroScope_730_ = lean_ctor_get(v_a_683_, 2);
v_ref_731_ = lean_ctor_get(v_a_683_, 5);
v___x_732_ = 0;
v___x_733_ = l_Lean_SourceInfo_fromRef(v_ref_731_, v___x_732_);
v___x_734_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__34, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__34_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__34);
v___x_735_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__36));
lean_inc(v_currMacroScope_730_);
lean_inc(v_quotContext_729_);
v___x_736_ = l_Lean_addMacroScope(v_quotContext_729_, v___x_735_, v_currMacroScope_730_);
v___x_737_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__40));
v___x_738_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_738_, 0, v___x_733_);
lean_ctor_set(v___x_738_, 1, v___x_734_);
lean_ctor_set(v___x_738_, 2, v___x_736_);
lean_ctor_set(v___x_738_, 3, v___x_737_);
v___x_739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_739_, 0, v___x_738_);
lean_ctor_set(v___x_739_, 1, v_a_684_);
return v___x_739_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___boxed(lean_object* v_x_740_, lean_object* v_a_741_, lean_object* v_a_742_){
_start:
{
uint8_t v_x_6708__boxed_743_; lean_object* v_res_744_; 
v_x_6708__boxed_743_ = lean_unbox(v_x_740_);
v_res_744_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX(v_x_6708__boxed_743_, v_a_741_, v_a_742_);
lean_dec_ref(v_a_741_);
return v_res_744_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__1(void){
_start:
{
lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_746_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__0));
v___x_747_ = l_String_toRawSubstring_x27(v___x_746_);
return v___x_747_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__9(void){
_start:
{
lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_766_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__8));
v___x_767_ = l_String_toRawSubstring_x27(v___x_766_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO(uint8_t v_x_784_, lean_object* v_a_785_, lean_object* v_a_786_){
_start:
{
if (v_x_784_ == 0)
{
lean_object* v_quotContext_787_; lean_object* v_currMacroScope_788_; lean_object* v_ref_789_; uint8_t v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; 
v_quotContext_787_ = lean_ctor_get(v_a_785_, 1);
v_currMacroScope_788_ = lean_ctor_get(v_a_785_, 2);
v_ref_789_ = lean_ctor_get(v_a_785_, 5);
v___x_790_ = 0;
v___x_791_ = l_Lean_SourceInfo_fromRef(v_ref_789_, v___x_790_);
v___x_792_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__1, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__1_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__1);
v___x_793_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__3));
lean_inc(v_currMacroScope_788_);
lean_inc(v_quotContext_787_);
v___x_794_ = l_Lean_addMacroScope(v_quotContext_787_, v___x_793_, v_currMacroScope_788_);
v___x_795_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__7));
v___x_796_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_796_, 0, v___x_791_);
lean_ctor_set(v___x_796_, 1, v___x_792_);
lean_ctor_set(v___x_796_, 2, v___x_794_);
lean_ctor_set(v___x_796_, 3, v___x_795_);
v___x_797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_797_, 0, v___x_796_);
lean_ctor_set(v___x_797_, 1, v_a_786_);
return v___x_797_;
}
else
{
lean_object* v_quotContext_798_; lean_object* v_currMacroScope_799_; lean_object* v_ref_800_; uint8_t v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
v_quotContext_798_ = lean_ctor_get(v_a_785_, 1);
v_currMacroScope_799_ = lean_ctor_get(v_a_785_, 2);
v_ref_800_ = lean_ctor_get(v_a_785_, 5);
v___x_801_ = 0;
v___x_802_ = l_Lean_SourceInfo_fromRef(v_ref_800_, v___x_801_);
v___x_803_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__9, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__9_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__9);
v___x_804_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__10));
lean_inc(v_currMacroScope_799_);
lean_inc(v_quotContext_798_);
v___x_805_ = l_Lean_addMacroScope(v_quotContext_798_, v___x_804_, v_currMacroScope_799_);
v___x_806_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__14));
v___x_807_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_807_, 0, v___x_802_);
lean_ctor_set(v___x_807_, 1, v___x_803_);
lean_ctor_set(v___x_807_, 2, v___x_805_);
lean_ctor_set(v___x_807_, 3, v___x_806_);
v___x_808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_808_, 0, v___x_807_);
lean_ctor_set(v___x_808_, 1, v_a_786_);
return v___x_808_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___boxed(lean_object* v_x_809_, lean_object* v_a_810_, lean_object* v_a_811_){
_start:
{
uint8_t v_x_2689__boxed_812_; lean_object* v_res_813_; 
v_x_2689__boxed_812_ = lean_unbox(v_x_809_);
v_res_813_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO(v_x_2689__boxed_812_, v_a_810_, v_a_811_);
lean_dec_ref(v_a_810_);
return v_res_813_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__1(void){
_start:
{
lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_815_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__0));
v___x_816_ = l_String_toRawSubstring_x27(v___x_815_);
return v___x_816_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__9(void){
_start:
{
lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_835_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__8));
v___x_836_ = l_String_toRawSubstring_x27(v___x_835_);
return v___x_836_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__16(void){
_start:
{
lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_854_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__15));
v___x_855_ = l_String_toRawSubstring_x27(v___x_854_);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ(uint8_t v_x_872_, lean_object* v_a_873_, lean_object* v_a_874_){
_start:
{
switch(v_x_872_)
{
case 0:
{
lean_object* v_quotContext_875_; lean_object* v_currMacroScope_876_; lean_object* v_ref_877_; uint8_t v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
v_quotContext_875_ = lean_ctor_get(v_a_873_, 1);
v_currMacroScope_876_ = lean_ctor_get(v_a_873_, 2);
v_ref_877_ = lean_ctor_get(v_a_873_, 5);
v___x_878_ = 0;
v___x_879_ = l_Lean_SourceInfo_fromRef(v_ref_877_, v___x_878_);
v___x_880_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__1, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__1_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__1);
v___x_881_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__3));
lean_inc(v_currMacroScope_876_);
lean_inc(v_quotContext_875_);
v___x_882_ = l_Lean_addMacroScope(v_quotContext_875_, v___x_881_, v_currMacroScope_876_);
v___x_883_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__7));
v___x_884_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_884_, 0, v___x_879_);
lean_ctor_set(v___x_884_, 1, v___x_880_);
lean_ctor_set(v___x_884_, 2, v___x_882_);
lean_ctor_set(v___x_884_, 3, v___x_883_);
v___x_885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_885_, 0, v___x_884_);
lean_ctor_set(v___x_885_, 1, v_a_874_);
return v___x_885_;
}
case 1:
{
lean_object* v_quotContext_886_; lean_object* v_currMacroScope_887_; lean_object* v_ref_888_; uint8_t v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; 
v_quotContext_886_ = lean_ctor_get(v_a_873_, 1);
v_currMacroScope_887_ = lean_ctor_get(v_a_873_, 2);
v_ref_888_ = lean_ctor_get(v_a_873_, 5);
v___x_889_ = 0;
v___x_890_ = l_Lean_SourceInfo_fromRef(v_ref_888_, v___x_889_);
v___x_891_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__9, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__9_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__9);
v___x_892_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__10));
lean_inc(v_currMacroScope_887_);
lean_inc(v_quotContext_886_);
v___x_893_ = l_Lean_addMacroScope(v_quotContext_886_, v___x_892_, v_currMacroScope_887_);
v___x_894_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__14));
v___x_895_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_895_, 0, v___x_890_);
lean_ctor_set(v___x_895_, 1, v___x_891_);
lean_ctor_set(v___x_895_, 2, v___x_893_);
lean_ctor_set(v___x_895_, 3, v___x_894_);
v___x_896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_896_, 0, v___x_895_);
lean_ctor_set(v___x_896_, 1, v_a_874_);
return v___x_896_;
}
default: 
{
lean_object* v_quotContext_897_; lean_object* v_currMacroScope_898_; lean_object* v_ref_899_; uint8_t v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; 
v_quotContext_897_ = lean_ctor_get(v_a_873_, 1);
v_currMacroScope_898_ = lean_ctor_get(v_a_873_, 2);
v_ref_899_ = lean_ctor_get(v_a_873_, 5);
v___x_900_ = 0;
v___x_901_ = l_Lean_SourceInfo_fromRef(v_ref_899_, v___x_900_);
v___x_902_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__16, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__16_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__16);
v___x_903_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__17));
lean_inc(v_currMacroScope_898_);
lean_inc(v_quotContext_897_);
v___x_904_ = l_Lean_addMacroScope(v_quotContext_897_, v___x_903_, v_currMacroScope_898_);
v___x_905_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__21));
v___x_906_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_906_, 0, v___x_901_);
lean_ctor_set(v___x_906_, 1, v___x_902_);
lean_ctor_set(v___x_906_, 2, v___x_904_);
lean_ctor_set(v___x_906_, 3, v___x_905_);
v___x_907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_907_, 0, v___x_906_);
lean_ctor_set(v___x_907_, 1, v_a_874_);
return v___x_907_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___boxed(lean_object* v_x_908_, lean_object* v_a_909_, lean_object* v_a_910_){
_start:
{
uint8_t v_x_4027__boxed_911_; lean_object* v_res_912_; 
v_x_4027__boxed_911_ = lean_unbox(v_x_908_);
v_res_912_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ(v_x_4027__boxed_911_, v_a_909_, v_a_910_);
lean_dec_ref(v_a_909_);
return v_res_912_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__1(void){
_start:
{
lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_914_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__0));
v___x_915_ = l_String_toRawSubstring_x27(v___x_914_);
return v___x_915_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__10(void){
_start:
{
lean_object* v___x_935_; lean_object* v___x_936_; 
v___x_935_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__9));
v___x_936_ = l_String_toRawSubstring_x27(v___x_935_);
return v___x_936_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__18(void){
_start:
{
lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_955_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__17));
v___x_956_ = l_String_toRawSubstring_x27(v___x_955_);
return v___x_956_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__26(void){
_start:
{
lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_975_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__25));
v___x_976_ = l_String_toRawSubstring_x27(v___x_975_);
return v___x_976_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__34(void){
_start:
{
lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_995_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__33));
v___x_996_ = l_String_toRawSubstring_x27(v___x_995_);
return v___x_996_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__49(void){
_start:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1031_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__48));
v___x_1032_ = l_String_toRawSubstring_x27(v___x_1031_);
return v___x_1032_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__70(void){
_start:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1081_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__69));
v___x_1082_ = l_String_toRawSubstring_x27(v___x_1081_);
return v___x_1082_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__74(void){
_start:
{
lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___x_1087_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__73));
v___x_1088_ = l_String_toRawSubstring_x27(v___x_1087_);
return v___x_1088_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__77(void){
_start:
{
lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1092_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__76));
v___x_1093_ = l_String_toRawSubstring_x27(v___x_1092_);
return v___x_1093_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__85(void){
_start:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1112_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__84));
v___x_1113_ = l_String_toRawSubstring_x27(v___x_1112_);
return v___x_1113_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__93(void){
_start:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; 
v___x_1132_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__92));
v___x_1133_ = l_String_toRawSubstring_x27(v___x_1132_);
return v___x_1133_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__101(void){
_start:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___x_1152_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__100));
v___x_1153_ = l_String_toRawSubstring_x27(v___x_1152_);
return v___x_1153_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__109(void){
_start:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; 
v___x_1172_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__108));
v___x_1173_ = l_String_toRawSubstring_x27(v___x_1172_);
return v___x_1173_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__117(void){
_start:
{
lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1192_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__116));
v___x_1193_ = l_String_toRawSubstring_x27(v___x_1192_);
return v___x_1193_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__125(void){
_start:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; 
v___x_1212_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__124));
v___x_1213_ = l_String_toRawSubstring_x27(v___x_1212_);
return v___x_1213_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__133(void){
_start:
{
lean_object* v___x_1232_; lean_object* v___x_1233_; 
v___x_1232_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__132));
v___x_1233_ = l_String_toRawSubstring_x27(v___x_1232_);
return v___x_1233_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__141(void){
_start:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1252_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__140));
v___x_1253_ = l_String_toRawSubstring_x27(v___x_1252_);
return v___x_1253_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__149(void){
_start:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1272_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__148));
v___x_1273_ = l_String_toRawSubstring_x27(v___x_1272_);
return v___x_1273_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__157(void){
_start:
{
lean_object* v___x_1292_; lean_object* v___x_1293_; 
v___x_1292_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__156));
v___x_1293_ = l_String_toRawSubstring_x27(v___x_1292_);
return v___x_1293_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__165(void){
_start:
{
lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1312_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__164));
v___x_1313_ = l_String_toRawSubstring_x27(v___x_1312_);
return v___x_1313_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__173(void){
_start:
{
lean_object* v___x_1332_; lean_object* v___x_1333_; 
v___x_1332_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__172));
v___x_1333_ = l_String_toRawSubstring_x27(v___x_1332_);
return v___x_1333_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__181(void){
_start:
{
lean_object* v___x_1352_; lean_object* v___x_1353_; 
v___x_1352_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__180));
v___x_1353_ = l_String_toRawSubstring_x27(v___x_1352_);
return v___x_1353_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__189(void){
_start:
{
lean_object* v___x_1372_; lean_object* v___x_1373_; 
v___x_1372_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__188));
v___x_1373_ = l_String_toRawSubstring_x27(v___x_1372_);
return v___x_1373_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__197(void){
_start:
{
lean_object* v___x_1392_; lean_object* v___x_1393_; 
v___x_1392_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__196));
v___x_1393_ = l_String_toRawSubstring_x27(v___x_1392_);
return v___x_1393_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__205(void){
_start:
{
lean_object* v___x_1412_; lean_object* v___x_1413_; 
v___x_1412_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__204));
v___x_1413_ = l_String_toRawSubstring_x27(v___x_1412_);
return v___x_1413_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__213(void){
_start:
{
lean_object* v___x_1432_; lean_object* v___x_1433_; 
v___x_1432_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__212));
v___x_1433_ = l_String_toRawSubstring_x27(v___x_1432_);
return v___x_1433_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__221(void){
_start:
{
lean_object* v___x_1452_; lean_object* v___x_1453_; 
v___x_1452_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__220));
v___x_1453_ = l_String_toRawSubstring_x27(v___x_1452_);
return v___x_1453_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__229(void){
_start:
{
lean_object* v___x_1472_; lean_object* v___x_1473_; 
v___x_1472_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__228));
v___x_1473_ = l_String_toRawSubstring_x27(v___x_1472_);
return v___x_1473_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__237(void){
_start:
{
lean_object* v___x_1492_; lean_object* v___x_1493_; 
v___x_1492_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__236));
v___x_1493_ = l_String_toRawSubstring_x27(v___x_1492_);
return v___x_1493_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__245(void){
_start:
{
lean_object* v___x_1512_; lean_object* v___x_1513_; 
v___x_1512_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__244));
v___x_1513_ = l_String_toRawSubstring_x27(v___x_1512_);
return v___x_1513_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__253(void){
_start:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___x_1532_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__252));
v___x_1533_ = l_String_toRawSubstring_x27(v___x_1532_);
return v___x_1533_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__261(void){
_start:
{
lean_object* v___x_1552_; lean_object* v___x_1553_; 
v___x_1552_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__260));
v___x_1553_ = l_String_toRawSubstring_x27(v___x_1552_);
return v___x_1553_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__269(void){
_start:
{
lean_object* v___x_1572_; lean_object* v___x_1573_; 
v___x_1572_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__268));
v___x_1573_ = l_String_toRawSubstring_x27(v___x_1572_);
return v___x_1573_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__277(void){
_start:
{
lean_object* v___x_1592_; lean_object* v___x_1593_; 
v___x_1592_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__276));
v___x_1593_ = l_String_toRawSubstring_x27(v___x_1592_);
return v___x_1593_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__285(void){
_start:
{
lean_object* v___x_1612_; lean_object* v___x_1613_; 
v___x_1612_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__284));
v___x_1613_ = l_String_toRawSubstring_x27(v___x_1612_);
return v___x_1613_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__293(void){
_start:
{
lean_object* v___x_1632_; lean_object* v___x_1633_; 
v___x_1632_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__292));
v___x_1633_ = l_String_toRawSubstring_x27(v___x_1632_);
return v___x_1633_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__301(void){
_start:
{
lean_object* v___x_1652_; lean_object* v___x_1653_; 
v___x_1652_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__300));
v___x_1653_ = l_String_toRawSubstring_x27(v___x_1652_);
return v___x_1653_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__309(void){
_start:
{
lean_object* v___x_1672_; lean_object* v___x_1673_; 
v___x_1672_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__308));
v___x_1673_ = l_String_toRawSubstring_x27(v___x_1672_);
return v___x_1673_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__317(void){
_start:
{
lean_object* v___x_1692_; lean_object* v___x_1693_; 
v___x_1692_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__316));
v___x_1693_ = l_String_toRawSubstring_x27(v___x_1692_);
return v___x_1693_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier(lean_object* v_x_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_){
_start:
{
switch(lean_obj_tag(v_x_1711_))
{
case 0:
{
uint8_t v_presentation_1714_; lean_object* v___x_1715_; lean_object* v_a_1716_; lean_object* v_a_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1738_; 
v_presentation_1714_ = lean_ctor_get_uint8(v_x_1711_, 0);
lean_dec_ref_known(v_x_1711_, 0);
v___x_1715_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertText(v_presentation_1714_, v_a_1712_, v_a_1713_);
v_a_1716_ = lean_ctor_get(v___x_1715_, 0);
v_a_1717_ = lean_ctor_get(v___x_1715_, 1);
v_isSharedCheck_1738_ = !lean_is_exclusive(v___x_1715_);
if (v_isSharedCheck_1738_ == 0)
{
v___x_1719_ = v___x_1715_;
v_isShared_1720_ = v_isSharedCheck_1738_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_a_1717_);
lean_inc(v_a_1716_);
lean_dec(v___x_1715_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1738_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v_quotContext_1721_; lean_object* v_currMacroScope_1722_; lean_object* v_ref_1723_; uint8_t v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1736_; 
v_quotContext_1721_ = lean_ctor_get(v_a_1712_, 1);
v_currMacroScope_1722_ = lean_ctor_get(v_a_1712_, 2);
v_ref_1723_ = lean_ctor_get(v_a_1712_, 5);
v___x_1724_ = 0;
v___x_1725_ = l_Lean_SourceInfo_fromRef(v_ref_1723_, v___x_1724_);
v___x_1726_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4));
v___x_1727_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__1, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__1_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__1);
v___x_1728_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__4));
lean_inc(v_currMacroScope_1722_);
lean_inc(v_quotContext_1721_);
v___x_1729_ = l_Lean_addMacroScope(v_quotContext_1721_, v___x_1728_, v_currMacroScope_1722_);
v___x_1730_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__8));
lean_inc_n(v___x_1725_, 2);
v___x_1731_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1731_, 0, v___x_1725_);
lean_ctor_set(v___x_1731_, 1, v___x_1727_);
lean_ctor_set(v___x_1731_, 2, v___x_1729_);
lean_ctor_set(v___x_1731_, 3, v___x_1730_);
v___x_1732_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15));
v___x_1733_ = l_Lean_Syntax_node1(v___x_1725_, v___x_1732_, v_a_1716_);
v___x_1734_ = l_Lean_Syntax_node2(v___x_1725_, v___x_1726_, v___x_1731_, v___x_1733_);
if (v_isShared_1720_ == 0)
{
lean_ctor_set(v___x_1719_, 0, v___x_1734_);
v___x_1736_ = v___x_1719_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v___x_1734_);
lean_ctor_set(v_reuseFailAlloc_1737_, 1, v_a_1717_);
v___x_1736_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
return v___x_1736_;
}
}
}
case 1:
{
lean_object* v_presentation_1739_; lean_object* v___x_1740_; lean_object* v_a_1741_; lean_object* v_a_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1763_; 
v_presentation_1739_ = lean_ctor_get(v_x_1711_, 0);
lean_inc(v_presentation_1739_);
lean_dec_ref_known(v_x_1711_, 1);
v___x_1740_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear(v_presentation_1739_, v_a_1712_, v_a_1713_);
v_a_1741_ = lean_ctor_get(v___x_1740_, 0);
v_a_1742_ = lean_ctor_get(v___x_1740_, 1);
v_isSharedCheck_1763_ = !lean_is_exclusive(v___x_1740_);
if (v_isSharedCheck_1763_ == 0)
{
v___x_1744_ = v___x_1740_;
v_isShared_1745_ = v_isSharedCheck_1763_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_a_1742_);
lean_inc(v_a_1741_);
lean_dec(v___x_1740_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1763_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
lean_object* v_quotContext_1746_; lean_object* v_currMacroScope_1747_; lean_object* v_ref_1748_; uint8_t v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1761_; 
v_quotContext_1746_ = lean_ctor_get(v_a_1712_, 1);
v_currMacroScope_1747_ = lean_ctor_get(v_a_1712_, 2);
v_ref_1748_ = lean_ctor_get(v_a_1712_, 5);
v___x_1749_ = 0;
v___x_1750_ = l_Lean_SourceInfo_fromRef(v_ref_1748_, v___x_1749_);
v___x_1751_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4));
v___x_1752_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__10, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__10_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__10);
v___x_1753_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__12));
lean_inc(v_currMacroScope_1747_);
lean_inc(v_quotContext_1746_);
v___x_1754_ = l_Lean_addMacroScope(v_quotContext_1746_, v___x_1753_, v_currMacroScope_1747_);
v___x_1755_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__16));
lean_inc_n(v___x_1750_, 2);
v___x_1756_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1756_, 0, v___x_1750_);
lean_ctor_set(v___x_1756_, 1, v___x_1752_);
lean_ctor_set(v___x_1756_, 2, v___x_1754_);
lean_ctor_set(v___x_1756_, 3, v___x_1755_);
v___x_1757_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15));
v___x_1758_ = l_Lean_Syntax_node1(v___x_1750_, v___x_1757_, v_a_1741_);
v___x_1759_ = l_Lean_Syntax_node2(v___x_1750_, v___x_1751_, v___x_1756_, v___x_1758_);
if (v_isShared_1745_ == 0)
{
lean_ctor_set(v___x_1744_, 0, v___x_1759_);
v___x_1761_ = v___x_1744_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v___x_1759_);
lean_ctor_set(v_reuseFailAlloc_1762_, 1, v_a_1742_);
v___x_1761_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
return v___x_1761_;
}
}
}
case 2:
{
lean_object* v_presentation_1764_; lean_object* v___x_1765_; lean_object* v_a_1766_; lean_object* v_a_1767_; lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1788_; 
v_presentation_1764_ = lean_ctor_get(v_x_1711_, 0);
lean_inc(v_presentation_1764_);
lean_dec_ref_known(v_x_1711_, 1);
v___x_1765_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear(v_presentation_1764_, v_a_1712_, v_a_1713_);
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
v_quotContext_1771_ = lean_ctor_get(v_a_1712_, 1);
v_currMacroScope_1772_ = lean_ctor_get(v_a_1712_, 2);
v_ref_1773_ = lean_ctor_get(v_a_1712_, 5);
v___x_1774_ = 0;
v___x_1775_ = l_Lean_SourceInfo_fromRef(v_ref_1773_, v___x_1774_);
v___x_1776_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4));
v___x_1777_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__18, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__18_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__18);
v___x_1778_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__20));
lean_inc(v_currMacroScope_1772_);
lean_inc(v_quotContext_1771_);
v___x_1779_ = l_Lean_addMacroScope(v_quotContext_1771_, v___x_1778_, v_currMacroScope_1772_);
v___x_1780_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__24));
lean_inc_n(v___x_1775_, 2);
v___x_1781_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1781_, 0, v___x_1775_);
lean_ctor_set(v___x_1781_, 1, v___x_1777_);
lean_ctor_set(v___x_1781_, 2, v___x_1779_);
lean_ctor_set(v___x_1781_, 3, v___x_1780_);
v___x_1782_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15));
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
case 3:
{
lean_object* v_presentation_1789_; lean_object* v___x_1790_; lean_object* v_a_1791_; lean_object* v_a_1792_; lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1813_; 
v_presentation_1789_ = lean_ctor_get(v_x_1711_, 0);
lean_inc(v_presentation_1789_);
lean_dec_ref_known(v_x_1711_, 1);
v___x_1790_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber(v_presentation_1789_, v_a_1712_, v_a_1713_);
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
v_quotContext_1796_ = lean_ctor_get(v_a_1712_, 1);
v_currMacroScope_1797_ = lean_ctor_get(v_a_1712_, 2);
v_ref_1798_ = lean_ctor_get(v_a_1712_, 5);
v___x_1799_ = 0;
v___x_1800_ = l_Lean_SourceInfo_fromRef(v_ref_1798_, v___x_1799_);
v___x_1801_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4));
v___x_1802_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__26, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__26_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__26);
v___x_1803_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__28));
lean_inc(v_currMacroScope_1797_);
lean_inc(v_quotContext_1796_);
v___x_1804_ = l_Lean_addMacroScope(v_quotContext_1796_, v___x_1803_, v_currMacroScope_1797_);
v___x_1805_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__32));
lean_inc_n(v___x_1800_, 2);
v___x_1806_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1806_, 0, v___x_1800_);
lean_ctor_set(v___x_1806_, 1, v___x_1802_);
lean_ctor_set(v___x_1806_, 2, v___x_1804_);
lean_ctor_set(v___x_1806_, 3, v___x_1805_);
v___x_1807_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15));
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
case 4:
{
lean_object* v_presentation_1814_; 
v_presentation_1814_ = lean_ctor_get(v_x_1711_, 0);
lean_inc_ref(v_presentation_1814_);
lean_dec_ref_known(v_x_1711_, 1);
if (lean_obj_tag(v_presentation_1814_) == 0)
{
lean_object* v_val_1815_; lean_object* v___x_1816_; lean_object* v_a_1817_; lean_object* v_a_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1865_; 
v_val_1815_ = lean_ctor_get(v_presentation_1814_, 0);
lean_inc(v_val_1815_);
lean_dec_ref_known(v_presentation_1814_, 1);
v___x_1816_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber(v_val_1815_, v_a_1712_, v_a_1713_);
v_a_1817_ = lean_ctor_get(v___x_1816_, 0);
v_a_1818_ = lean_ctor_get(v___x_1816_, 1);
v_isSharedCheck_1865_ = !lean_is_exclusive(v___x_1816_);
if (v_isSharedCheck_1865_ == 0)
{
v___x_1820_ = v___x_1816_;
v_isShared_1821_ = v_isSharedCheck_1865_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_a_1818_);
lean_inc(v_a_1817_);
lean_dec(v___x_1816_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1865_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
lean_object* v_quotContext_1822_; lean_object* v_currMacroScope_1823_; lean_object* v_ref_1824_; uint8_t v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1863_; 
v_quotContext_1822_ = lean_ctor_get(v_a_1712_, 1);
v_currMacroScope_1823_ = lean_ctor_get(v_a_1712_, 2);
v_ref_1824_ = lean_ctor_get(v_a_1712_, 5);
v___x_1825_ = 0;
v___x_1826_ = l_Lean_SourceInfo_fromRef(v_ref_1824_, v___x_1825_);
v___x_1827_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4));
v___x_1828_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__34, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__34_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__34);
v___x_1829_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__36));
lean_inc_n(v_currMacroScope_1823_, 3);
lean_inc_n(v_quotContext_1822_, 3);
v___x_1830_ = l_Lean_addMacroScope(v_quotContext_1822_, v___x_1829_, v_currMacroScope_1823_);
v___x_1831_ = lean_box(0);
v___x_1832_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__40));
lean_inc_n(v___x_1826_, 13);
v___x_1833_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1833_, 0, v___x_1826_);
lean_ctor_set(v___x_1833_, 1, v___x_1828_);
lean_ctor_set(v___x_1833_, 2, v___x_1830_);
lean_ctor_set(v___x_1833_, 3, v___x_1832_);
v___x_1834_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15));
v___x_1835_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__42));
v___x_1836_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__44));
v___x_1837_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__45));
v___x_1838_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1838_, 0, v___x_1826_);
lean_ctor_set(v___x_1838_, 1, v___x_1837_);
v___x_1839_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__47));
v___x_1840_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__49, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__49_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__49);
v___x_1841_ = lean_box(0);
v___x_1842_ = l_Lean_addMacroScope(v_quotContext_1822_, v___x_1841_, v_currMacroScope_1823_);
v___x_1843_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__65));
v___x_1844_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1826_);
lean_ctor_set(v___x_1844_, 1, v___x_1840_);
lean_ctor_set(v___x_1844_, 2, v___x_1842_);
lean_ctor_set(v___x_1844_, 3, v___x_1843_);
v___x_1845_ = l_Lean_Syntax_node1(v___x_1826_, v___x_1839_, v___x_1844_);
v___x_1846_ = l_Lean_Syntax_node2(v___x_1826_, v___x_1836_, v___x_1838_, v___x_1845_);
v___x_1847_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__67));
v___x_1848_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__68));
v___x_1849_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1849_, 0, v___x_1826_);
lean_ctor_set(v___x_1849_, 1, v___x_1848_);
v___x_1850_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__70, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__70_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__70);
v___x_1851_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__71));
v___x_1852_ = l_Lean_addMacroScope(v_quotContext_1822_, v___x_1851_, v_currMacroScope_1823_);
v___x_1853_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1853_, 0, v___x_1826_);
lean_ctor_set(v___x_1853_, 1, v___x_1850_);
lean_ctor_set(v___x_1853_, 2, v___x_1852_);
lean_ctor_set(v___x_1853_, 3, v___x_1831_);
v___x_1854_ = l_Lean_Syntax_node2(v___x_1826_, v___x_1847_, v___x_1849_, v___x_1853_);
v___x_1855_ = l_Lean_Syntax_node1(v___x_1826_, v___x_1834_, v_a_1817_);
v___x_1856_ = l_Lean_Syntax_node2(v___x_1826_, v___x_1827_, v___x_1854_, v___x_1855_);
v___x_1857_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__72));
v___x_1858_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1858_, 0, v___x_1826_);
lean_ctor_set(v___x_1858_, 1, v___x_1857_);
v___x_1859_ = l_Lean_Syntax_node3(v___x_1826_, v___x_1835_, v___x_1846_, v___x_1856_, v___x_1858_);
v___x_1860_ = l_Lean_Syntax_node1(v___x_1826_, v___x_1834_, v___x_1859_);
v___x_1861_ = l_Lean_Syntax_node2(v___x_1826_, v___x_1827_, v___x_1833_, v___x_1860_);
if (v_isShared_1821_ == 0)
{
lean_ctor_set(v___x_1820_, 0, v___x_1861_);
v___x_1863_ = v___x_1820_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v___x_1861_);
lean_ctor_set(v_reuseFailAlloc_1864_, 1, v_a_1818_);
v___x_1863_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
return v___x_1863_;
}
}
}
else
{
lean_object* v_val_1866_; uint8_t v___x_1867_; lean_object* v___x_1868_; lean_object* v_a_1869_; lean_object* v_a_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1917_; 
v_val_1866_ = lean_ctor_get(v_presentation_1814_, 0);
lean_inc(v_val_1866_);
lean_dec_ref_known(v_presentation_1814_, 1);
v___x_1867_ = lean_unbox(v_val_1866_);
lean_dec(v_val_1866_);
v___x_1868_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertText(v___x_1867_, v_a_1712_, v_a_1713_);
v_a_1869_ = lean_ctor_get(v___x_1868_, 0);
v_a_1870_ = lean_ctor_get(v___x_1868_, 1);
v_isSharedCheck_1917_ = !lean_is_exclusive(v___x_1868_);
if (v_isSharedCheck_1917_ == 0)
{
v___x_1872_ = v___x_1868_;
v_isShared_1873_ = v_isSharedCheck_1917_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_a_1870_);
lean_inc(v_a_1869_);
lean_dec(v___x_1868_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1917_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v_quotContext_1874_; lean_object* v_currMacroScope_1875_; lean_object* v_ref_1876_; uint8_t v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1915_; 
v_quotContext_1874_ = lean_ctor_get(v_a_1712_, 1);
v_currMacroScope_1875_ = lean_ctor_get(v_a_1712_, 2);
v_ref_1876_ = lean_ctor_get(v_a_1712_, 5);
v___x_1877_ = 0;
v___x_1878_ = l_Lean_SourceInfo_fromRef(v_ref_1876_, v___x_1877_);
v___x_1879_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4));
v___x_1880_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__34, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__34_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__34);
v___x_1881_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__36));
lean_inc_n(v_currMacroScope_1875_, 3);
lean_inc_n(v_quotContext_1874_, 3);
v___x_1882_ = l_Lean_addMacroScope(v_quotContext_1874_, v___x_1881_, v_currMacroScope_1875_);
v___x_1883_ = lean_box(0);
v___x_1884_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__40));
lean_inc_n(v___x_1878_, 13);
v___x_1885_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1885_, 0, v___x_1878_);
lean_ctor_set(v___x_1885_, 1, v___x_1880_);
lean_ctor_set(v___x_1885_, 2, v___x_1882_);
lean_ctor_set(v___x_1885_, 3, v___x_1884_);
v___x_1886_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15));
v___x_1887_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__42));
v___x_1888_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__44));
v___x_1889_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__45));
v___x_1890_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1890_, 0, v___x_1878_);
lean_ctor_set(v___x_1890_, 1, v___x_1889_);
v___x_1891_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__47));
v___x_1892_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__49, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__49_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__49);
v___x_1893_ = lean_box(0);
v___x_1894_ = l_Lean_addMacroScope(v_quotContext_1874_, v___x_1893_, v_currMacroScope_1875_);
v___x_1895_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__65));
v___x_1896_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1896_, 0, v___x_1878_);
lean_ctor_set(v___x_1896_, 1, v___x_1892_);
lean_ctor_set(v___x_1896_, 2, v___x_1894_);
lean_ctor_set(v___x_1896_, 3, v___x_1895_);
v___x_1897_ = l_Lean_Syntax_node1(v___x_1878_, v___x_1891_, v___x_1896_);
v___x_1898_ = l_Lean_Syntax_node2(v___x_1878_, v___x_1888_, v___x_1890_, v___x_1897_);
v___x_1899_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__67));
v___x_1900_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__68));
v___x_1901_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1901_, 0, v___x_1878_);
lean_ctor_set(v___x_1901_, 1, v___x_1900_);
v___x_1902_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__74, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__74_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__74);
v___x_1903_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__75));
v___x_1904_ = l_Lean_addMacroScope(v_quotContext_1874_, v___x_1903_, v_currMacroScope_1875_);
v___x_1905_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1905_, 0, v___x_1878_);
lean_ctor_set(v___x_1905_, 1, v___x_1902_);
lean_ctor_set(v___x_1905_, 2, v___x_1904_);
lean_ctor_set(v___x_1905_, 3, v___x_1883_);
v___x_1906_ = l_Lean_Syntax_node2(v___x_1878_, v___x_1899_, v___x_1901_, v___x_1905_);
v___x_1907_ = l_Lean_Syntax_node1(v___x_1878_, v___x_1886_, v_a_1869_);
v___x_1908_ = l_Lean_Syntax_node2(v___x_1878_, v___x_1879_, v___x_1906_, v___x_1907_);
v___x_1909_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__72));
v___x_1910_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1910_, 0, v___x_1878_);
lean_ctor_set(v___x_1910_, 1, v___x_1909_);
v___x_1911_ = l_Lean_Syntax_node3(v___x_1878_, v___x_1887_, v___x_1898_, v___x_1908_, v___x_1910_);
v___x_1912_ = l_Lean_Syntax_node1(v___x_1878_, v___x_1886_, v___x_1911_);
v___x_1913_ = l_Lean_Syntax_node2(v___x_1878_, v___x_1879_, v___x_1885_, v___x_1912_);
if (v_isShared_1873_ == 0)
{
lean_ctor_set(v___x_1872_, 0, v___x_1913_);
v___x_1915_ = v___x_1872_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v___x_1913_);
lean_ctor_set(v_reuseFailAlloc_1916_, 1, v_a_1870_);
v___x_1915_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
return v___x_1915_;
}
}
}
}
case 5:
{
lean_object* v_presentation_1918_; 
v_presentation_1918_ = lean_ctor_get(v_x_1711_, 0);
lean_inc_ref(v_presentation_1918_);
lean_dec_ref_known(v_x_1711_, 1);
if (lean_obj_tag(v_presentation_1918_) == 0)
{
lean_object* v_val_1919_; lean_object* v___x_1920_; lean_object* v_a_1921_; lean_object* v_a_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1969_; 
v_val_1919_ = lean_ctor_get(v_presentation_1918_, 0);
lean_inc(v_val_1919_);
lean_dec_ref_known(v_presentation_1918_, 1);
v___x_1920_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber(v_val_1919_, v_a_1712_, v_a_1713_);
v_a_1921_ = lean_ctor_get(v___x_1920_, 0);
v_a_1922_ = lean_ctor_get(v___x_1920_, 1);
v_isSharedCheck_1969_ = !lean_is_exclusive(v___x_1920_);
if (v_isSharedCheck_1969_ == 0)
{
v___x_1924_ = v___x_1920_;
v_isShared_1925_ = v_isSharedCheck_1969_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_a_1922_);
lean_inc(v_a_1921_);
lean_dec(v___x_1920_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1969_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
lean_object* v_quotContext_1926_; lean_object* v_currMacroScope_1927_; lean_object* v_ref_1928_; uint8_t v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1967_; 
v_quotContext_1926_ = lean_ctor_get(v_a_1712_, 1);
v_currMacroScope_1927_ = lean_ctor_get(v_a_1712_, 2);
v_ref_1928_ = lean_ctor_get(v_a_1712_, 5);
v___x_1929_ = 0;
v___x_1930_ = l_Lean_SourceInfo_fromRef(v_ref_1928_, v___x_1929_);
v___x_1931_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4));
v___x_1932_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__77, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__77_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__77);
v___x_1933_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__79));
lean_inc_n(v_currMacroScope_1927_, 3);
lean_inc_n(v_quotContext_1926_, 3);
v___x_1934_ = l_Lean_addMacroScope(v_quotContext_1926_, v___x_1933_, v_currMacroScope_1927_);
v___x_1935_ = lean_box(0);
v___x_1936_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__83));
lean_inc_n(v___x_1930_, 13);
v___x_1937_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1937_, 0, v___x_1930_);
lean_ctor_set(v___x_1937_, 1, v___x_1932_);
lean_ctor_set(v___x_1937_, 2, v___x_1934_);
lean_ctor_set(v___x_1937_, 3, v___x_1936_);
v___x_1938_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15));
v___x_1939_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__42));
v___x_1940_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__44));
v___x_1941_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__45));
v___x_1942_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1942_, 0, v___x_1930_);
lean_ctor_set(v___x_1942_, 1, v___x_1941_);
v___x_1943_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__47));
v___x_1944_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__49, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__49_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__49);
v___x_1945_ = lean_box(0);
v___x_1946_ = l_Lean_addMacroScope(v_quotContext_1926_, v___x_1945_, v_currMacroScope_1927_);
v___x_1947_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__65));
v___x_1948_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1948_, 0, v___x_1930_);
lean_ctor_set(v___x_1948_, 1, v___x_1944_);
lean_ctor_set(v___x_1948_, 2, v___x_1946_);
lean_ctor_set(v___x_1948_, 3, v___x_1947_);
v___x_1949_ = l_Lean_Syntax_node1(v___x_1930_, v___x_1943_, v___x_1948_);
v___x_1950_ = l_Lean_Syntax_node2(v___x_1930_, v___x_1940_, v___x_1942_, v___x_1949_);
v___x_1951_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__67));
v___x_1952_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__68));
v___x_1953_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1953_, 0, v___x_1930_);
lean_ctor_set(v___x_1953_, 1, v___x_1952_);
v___x_1954_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__70, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__70_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__70);
v___x_1955_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__71));
v___x_1956_ = l_Lean_addMacroScope(v_quotContext_1926_, v___x_1955_, v_currMacroScope_1927_);
v___x_1957_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1957_, 0, v___x_1930_);
lean_ctor_set(v___x_1957_, 1, v___x_1954_);
lean_ctor_set(v___x_1957_, 2, v___x_1956_);
lean_ctor_set(v___x_1957_, 3, v___x_1935_);
v___x_1958_ = l_Lean_Syntax_node2(v___x_1930_, v___x_1951_, v___x_1953_, v___x_1957_);
v___x_1959_ = l_Lean_Syntax_node1(v___x_1930_, v___x_1938_, v_a_1921_);
v___x_1960_ = l_Lean_Syntax_node2(v___x_1930_, v___x_1931_, v___x_1958_, v___x_1959_);
v___x_1961_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__72));
v___x_1962_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1962_, 0, v___x_1930_);
lean_ctor_set(v___x_1962_, 1, v___x_1961_);
v___x_1963_ = l_Lean_Syntax_node3(v___x_1930_, v___x_1939_, v___x_1950_, v___x_1960_, v___x_1962_);
v___x_1964_ = l_Lean_Syntax_node1(v___x_1930_, v___x_1938_, v___x_1963_);
v___x_1965_ = l_Lean_Syntax_node2(v___x_1930_, v___x_1931_, v___x_1937_, v___x_1964_);
if (v_isShared_1925_ == 0)
{
lean_ctor_set(v___x_1924_, 0, v___x_1965_);
v___x_1967_ = v___x_1924_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v___x_1965_);
lean_ctor_set(v_reuseFailAlloc_1968_, 1, v_a_1922_);
v___x_1967_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
return v___x_1967_;
}
}
}
else
{
lean_object* v_val_1970_; uint8_t v___x_1971_; lean_object* v___x_1972_; lean_object* v_a_1973_; lean_object* v_a_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_2021_; 
v_val_1970_ = lean_ctor_get(v_presentation_1918_, 0);
lean_inc(v_val_1970_);
lean_dec_ref_known(v_presentation_1918_, 1);
v___x_1971_ = lean_unbox(v_val_1970_);
lean_dec(v_val_1970_);
v___x_1972_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertText(v___x_1971_, v_a_1712_, v_a_1713_);
v_a_1973_ = lean_ctor_get(v___x_1972_, 0);
v_a_1974_ = lean_ctor_get(v___x_1972_, 1);
v_isSharedCheck_2021_ = !lean_is_exclusive(v___x_1972_);
if (v_isSharedCheck_2021_ == 0)
{
v___x_1976_ = v___x_1972_;
v_isShared_1977_ = v_isSharedCheck_2021_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_a_1974_);
lean_inc(v_a_1973_);
lean_dec(v___x_1972_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_2021_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
lean_object* v_quotContext_1978_; lean_object* v_currMacroScope_1979_; lean_object* v_ref_1980_; uint8_t v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2019_; 
v_quotContext_1978_ = lean_ctor_get(v_a_1712_, 1);
v_currMacroScope_1979_ = lean_ctor_get(v_a_1712_, 2);
v_ref_1980_ = lean_ctor_get(v_a_1712_, 5);
v___x_1981_ = 0;
v___x_1982_ = l_Lean_SourceInfo_fromRef(v_ref_1980_, v___x_1981_);
v___x_1983_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4));
v___x_1984_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__77, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__77_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__77);
v___x_1985_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__79));
lean_inc_n(v_currMacroScope_1979_, 3);
lean_inc_n(v_quotContext_1978_, 3);
v___x_1986_ = l_Lean_addMacroScope(v_quotContext_1978_, v___x_1985_, v_currMacroScope_1979_);
v___x_1987_ = lean_box(0);
v___x_1988_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__83));
lean_inc_n(v___x_1982_, 13);
v___x_1989_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1989_, 0, v___x_1982_);
lean_ctor_set(v___x_1989_, 1, v___x_1984_);
lean_ctor_set(v___x_1989_, 2, v___x_1986_);
lean_ctor_set(v___x_1989_, 3, v___x_1988_);
v___x_1990_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15));
v___x_1991_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__42));
v___x_1992_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__44));
v___x_1993_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__45));
v___x_1994_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1994_, 0, v___x_1982_);
lean_ctor_set(v___x_1994_, 1, v___x_1993_);
v___x_1995_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__47));
v___x_1996_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__49, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__49_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__49);
v___x_1997_ = lean_box(0);
v___x_1998_ = l_Lean_addMacroScope(v_quotContext_1978_, v___x_1997_, v_currMacroScope_1979_);
v___x_1999_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__65));
v___x_2000_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2000_, 0, v___x_1982_);
lean_ctor_set(v___x_2000_, 1, v___x_1996_);
lean_ctor_set(v___x_2000_, 2, v___x_1998_);
lean_ctor_set(v___x_2000_, 3, v___x_1999_);
v___x_2001_ = l_Lean_Syntax_node1(v___x_1982_, v___x_1995_, v___x_2000_);
v___x_2002_ = l_Lean_Syntax_node2(v___x_1982_, v___x_1992_, v___x_1994_, v___x_2001_);
v___x_2003_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__67));
v___x_2004_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__68));
v___x_2005_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2005_, 0, v___x_1982_);
lean_ctor_set(v___x_2005_, 1, v___x_2004_);
v___x_2006_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__74, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__74_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__74);
v___x_2007_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__75));
v___x_2008_ = l_Lean_addMacroScope(v_quotContext_1978_, v___x_2007_, v_currMacroScope_1979_);
v___x_2009_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2009_, 0, v___x_1982_);
lean_ctor_set(v___x_2009_, 1, v___x_2006_);
lean_ctor_set(v___x_2009_, 2, v___x_2008_);
lean_ctor_set(v___x_2009_, 3, v___x_1987_);
v___x_2010_ = l_Lean_Syntax_node2(v___x_1982_, v___x_2003_, v___x_2005_, v___x_2009_);
v___x_2011_ = l_Lean_Syntax_node1(v___x_1982_, v___x_1990_, v_a_1973_);
v___x_2012_ = l_Lean_Syntax_node2(v___x_1982_, v___x_1983_, v___x_2010_, v___x_2011_);
v___x_2013_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__72));
v___x_2014_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2014_, 0, v___x_1982_);
lean_ctor_set(v___x_2014_, 1, v___x_2013_);
v___x_2015_ = l_Lean_Syntax_node3(v___x_1982_, v___x_1991_, v___x_2002_, v___x_2012_, v___x_2014_);
v___x_2016_ = l_Lean_Syntax_node1(v___x_1982_, v___x_1990_, v___x_2015_);
v___x_2017_ = l_Lean_Syntax_node2(v___x_1982_, v___x_1983_, v___x_1989_, v___x_2016_);
if (v_isShared_1977_ == 0)
{
lean_ctor_set(v___x_1976_, 0, v___x_2017_);
v___x_2019_ = v___x_1976_;
goto v_reusejp_2018_;
}
else
{
lean_object* v_reuseFailAlloc_2020_; 
v_reuseFailAlloc_2020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2020_, 0, v___x_2017_);
lean_ctor_set(v_reuseFailAlloc_2020_, 1, v_a_1974_);
v___x_2019_ = v_reuseFailAlloc_2020_;
goto v_reusejp_2018_;
}
v_reusejp_2018_:
{
return v___x_2019_;
}
}
}
}
case 6:
{
lean_object* v_presentation_2022_; lean_object* v___x_2023_; lean_object* v_a_2024_; lean_object* v_a_2025_; lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2046_; 
v_presentation_2022_ = lean_ctor_get(v_x_1711_, 0);
lean_inc(v_presentation_2022_);
lean_dec_ref_known(v_x_1711_, 1);
v___x_2023_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber(v_presentation_2022_, v_a_1712_, v_a_1713_);
v_a_2024_ = lean_ctor_get(v___x_2023_, 0);
v_a_2025_ = lean_ctor_get(v___x_2023_, 1);
v_isSharedCheck_2046_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2046_ == 0)
{
v___x_2027_ = v___x_2023_;
v_isShared_2028_ = v_isSharedCheck_2046_;
goto v_resetjp_2026_;
}
else
{
lean_inc(v_a_2025_);
lean_inc(v_a_2024_);
lean_dec(v___x_2023_);
v___x_2027_ = lean_box(0);
v_isShared_2028_ = v_isSharedCheck_2046_;
goto v_resetjp_2026_;
}
v_resetjp_2026_:
{
lean_object* v_quotContext_2029_; lean_object* v_currMacroScope_2030_; lean_object* v_ref_2031_; uint8_t v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2044_; 
v_quotContext_2029_ = lean_ctor_get(v_a_1712_, 1);
v_currMacroScope_2030_ = lean_ctor_get(v_a_1712_, 2);
v_ref_2031_ = lean_ctor_get(v_a_1712_, 5);
v___x_2032_ = 0;
v___x_2033_ = l_Lean_SourceInfo_fromRef(v_ref_2031_, v___x_2032_);
v___x_2034_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4));
v___x_2035_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__85, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__85_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__85);
v___x_2036_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__87));
lean_inc(v_currMacroScope_2030_);
lean_inc(v_quotContext_2029_);
v___x_2037_ = l_Lean_addMacroScope(v_quotContext_2029_, v___x_2036_, v_currMacroScope_2030_);
v___x_2038_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__91));
lean_inc_n(v___x_2033_, 2);
v___x_2039_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2039_, 0, v___x_2033_);
lean_ctor_set(v___x_2039_, 1, v___x_2035_);
lean_ctor_set(v___x_2039_, 2, v___x_2037_);
lean_ctor_set(v___x_2039_, 3, v___x_2038_);
v___x_2040_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15));
v___x_2041_ = l_Lean_Syntax_node1(v___x_2033_, v___x_2040_, v_a_2024_);
v___x_2042_ = l_Lean_Syntax_node2(v___x_2033_, v___x_2034_, v___x_2039_, v___x_2041_);
if (v_isShared_2028_ == 0)
{
lean_ctor_set(v___x_2027_, 0, v___x_2042_);
v___x_2044_ = v___x_2027_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v___x_2042_);
lean_ctor_set(v_reuseFailAlloc_2045_, 1, v_a_2025_);
v___x_2044_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
return v___x_2044_;
}
}
}
case 7:
{
lean_object* v_presentation_2047_; 
v_presentation_2047_ = lean_ctor_get(v_x_1711_, 0);
lean_inc_ref(v_presentation_2047_);
lean_dec_ref_known(v_x_1711_, 1);
if (lean_obj_tag(v_presentation_2047_) == 0)
{
lean_object* v_val_2048_; lean_object* v___x_2049_; lean_object* v_a_2050_; lean_object* v_a_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2098_; 
v_val_2048_ = lean_ctor_get(v_presentation_2047_, 0);
lean_inc(v_val_2048_);
lean_dec_ref_known(v_presentation_2047_, 1);
v___x_2049_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber(v_val_2048_, v_a_1712_, v_a_1713_);
v_a_2050_ = lean_ctor_get(v___x_2049_, 0);
v_a_2051_ = lean_ctor_get(v___x_2049_, 1);
v_isSharedCheck_2098_ = !lean_is_exclusive(v___x_2049_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_2053_ = v___x_2049_;
v_isShared_2054_ = v_isSharedCheck_2098_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_a_2051_);
lean_inc(v_a_2050_);
lean_dec(v___x_2049_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2098_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v_quotContext_2055_; lean_object* v_currMacroScope_2056_; lean_object* v_ref_2057_; uint8_t v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2096_; 
v_quotContext_2055_ = lean_ctor_get(v_a_1712_, 1);
v_currMacroScope_2056_ = lean_ctor_get(v_a_1712_, 2);
v_ref_2057_ = lean_ctor_get(v_a_1712_, 5);
v___x_2058_ = 0;
v___x_2059_ = l_Lean_SourceInfo_fromRef(v_ref_2057_, v___x_2058_);
v___x_2060_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4));
v___x_2061_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__93, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__93_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__93);
v___x_2062_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__95));
lean_inc_n(v_currMacroScope_2056_, 3);
lean_inc_n(v_quotContext_2055_, 3);
v___x_2063_ = l_Lean_addMacroScope(v_quotContext_2055_, v___x_2062_, v_currMacroScope_2056_);
v___x_2064_ = lean_box(0);
v___x_2065_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__99));
lean_inc_n(v___x_2059_, 13);
v___x_2066_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2066_, 0, v___x_2059_);
lean_ctor_set(v___x_2066_, 1, v___x_2061_);
lean_ctor_set(v___x_2066_, 2, v___x_2063_);
lean_ctor_set(v___x_2066_, 3, v___x_2065_);
v___x_2067_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15));
v___x_2068_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__42));
v___x_2069_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__44));
v___x_2070_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__45));
v___x_2071_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2071_, 0, v___x_2059_);
lean_ctor_set(v___x_2071_, 1, v___x_2070_);
v___x_2072_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__47));
v___x_2073_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__49, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__49_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__49);
v___x_2074_ = lean_box(0);
v___x_2075_ = l_Lean_addMacroScope(v_quotContext_2055_, v___x_2074_, v_currMacroScope_2056_);
v___x_2076_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__65));
v___x_2077_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2077_, 0, v___x_2059_);
lean_ctor_set(v___x_2077_, 1, v___x_2073_);
lean_ctor_set(v___x_2077_, 2, v___x_2075_);
lean_ctor_set(v___x_2077_, 3, v___x_2076_);
v___x_2078_ = l_Lean_Syntax_node1(v___x_2059_, v___x_2072_, v___x_2077_);
v___x_2079_ = l_Lean_Syntax_node2(v___x_2059_, v___x_2069_, v___x_2071_, v___x_2078_);
v___x_2080_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__67));
v___x_2081_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__68));
v___x_2082_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2082_, 0, v___x_2059_);
lean_ctor_set(v___x_2082_, 1, v___x_2081_);
v___x_2083_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__70, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__70_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__70);
v___x_2084_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__71));
v___x_2085_ = l_Lean_addMacroScope(v_quotContext_2055_, v___x_2084_, v_currMacroScope_2056_);
v___x_2086_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2086_, 0, v___x_2059_);
lean_ctor_set(v___x_2086_, 1, v___x_2083_);
lean_ctor_set(v___x_2086_, 2, v___x_2085_);
lean_ctor_set(v___x_2086_, 3, v___x_2064_);
v___x_2087_ = l_Lean_Syntax_node2(v___x_2059_, v___x_2080_, v___x_2082_, v___x_2086_);
v___x_2088_ = l_Lean_Syntax_node1(v___x_2059_, v___x_2067_, v_a_2050_);
v___x_2089_ = l_Lean_Syntax_node2(v___x_2059_, v___x_2060_, v___x_2087_, v___x_2088_);
v___x_2090_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__72));
v___x_2091_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2091_, 0, v___x_2059_);
lean_ctor_set(v___x_2091_, 1, v___x_2090_);
v___x_2092_ = l_Lean_Syntax_node3(v___x_2059_, v___x_2068_, v___x_2079_, v___x_2089_, v___x_2091_);
v___x_2093_ = l_Lean_Syntax_node1(v___x_2059_, v___x_2067_, v___x_2092_);
v___x_2094_ = l_Lean_Syntax_node2(v___x_2059_, v___x_2060_, v___x_2066_, v___x_2093_);
if (v_isShared_2054_ == 0)
{
lean_ctor_set(v___x_2053_, 0, v___x_2094_);
v___x_2096_ = v___x_2053_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v___x_2094_);
lean_ctor_set(v_reuseFailAlloc_2097_, 1, v_a_2051_);
v___x_2096_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
return v___x_2096_;
}
}
}
else
{
lean_object* v_val_2099_; uint8_t v___x_2100_; lean_object* v___x_2101_; lean_object* v_a_2102_; lean_object* v_a_2103_; lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2150_; 
v_val_2099_ = lean_ctor_get(v_presentation_2047_, 0);
lean_inc(v_val_2099_);
lean_dec_ref_known(v_presentation_2047_, 1);
v___x_2100_ = lean_unbox(v_val_2099_);
lean_dec(v_val_2099_);
v___x_2101_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertText(v___x_2100_, v_a_1712_, v_a_1713_);
v_a_2102_ = lean_ctor_get(v___x_2101_, 0);
v_a_2103_ = lean_ctor_get(v___x_2101_, 1);
v_isSharedCheck_2150_ = !lean_is_exclusive(v___x_2101_);
if (v_isSharedCheck_2150_ == 0)
{
v___x_2105_ = v___x_2101_;
v_isShared_2106_ = v_isSharedCheck_2150_;
goto v_resetjp_2104_;
}
else
{
lean_inc(v_a_2103_);
lean_inc(v_a_2102_);
lean_dec(v___x_2101_);
v___x_2105_ = lean_box(0);
v_isShared_2106_ = v_isSharedCheck_2150_;
goto v_resetjp_2104_;
}
v_resetjp_2104_:
{
lean_object* v_quotContext_2107_; lean_object* v_currMacroScope_2108_; lean_object* v_ref_2109_; uint8_t v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2148_; 
v_quotContext_2107_ = lean_ctor_get(v_a_1712_, 1);
v_currMacroScope_2108_ = lean_ctor_get(v_a_1712_, 2);
v_ref_2109_ = lean_ctor_get(v_a_1712_, 5);
v___x_2110_ = 0;
v___x_2111_ = l_Lean_SourceInfo_fromRef(v_ref_2109_, v___x_2110_);
v___x_2112_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4));
v___x_2113_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__93, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__93_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__93);
v___x_2114_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__95));
lean_inc_n(v_currMacroScope_2108_, 3);
lean_inc_n(v_quotContext_2107_, 3);
v___x_2115_ = l_Lean_addMacroScope(v_quotContext_2107_, v___x_2114_, v_currMacroScope_2108_);
v___x_2116_ = lean_box(0);
v___x_2117_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__99));
lean_inc_n(v___x_2111_, 13);
v___x_2118_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2111_);
lean_ctor_set(v___x_2118_, 1, v___x_2113_);
lean_ctor_set(v___x_2118_, 2, v___x_2115_);
lean_ctor_set(v___x_2118_, 3, v___x_2117_);
v___x_2119_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15));
v___x_2120_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__42));
v___x_2121_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__44));
v___x_2122_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__45));
v___x_2123_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2123_, 0, v___x_2111_);
lean_ctor_set(v___x_2123_, 1, v___x_2122_);
v___x_2124_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__47));
v___x_2125_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__49, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__49_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__49);
v___x_2126_ = lean_box(0);
v___x_2127_ = l_Lean_addMacroScope(v_quotContext_2107_, v___x_2126_, v_currMacroScope_2108_);
v___x_2128_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__65));
v___x_2129_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2129_, 0, v___x_2111_);
lean_ctor_set(v___x_2129_, 1, v___x_2125_);
lean_ctor_set(v___x_2129_, 2, v___x_2127_);
lean_ctor_set(v___x_2129_, 3, v___x_2128_);
v___x_2130_ = l_Lean_Syntax_node1(v___x_2111_, v___x_2124_, v___x_2129_);
v___x_2131_ = l_Lean_Syntax_node2(v___x_2111_, v___x_2121_, v___x_2123_, v___x_2130_);
v___x_2132_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__67));
v___x_2133_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__68));
v___x_2134_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2134_, 0, v___x_2111_);
lean_ctor_set(v___x_2134_, 1, v___x_2133_);
v___x_2135_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__74, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__74_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__74);
v___x_2136_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__75));
v___x_2137_ = l_Lean_addMacroScope(v_quotContext_2107_, v___x_2136_, v_currMacroScope_2108_);
v___x_2138_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2138_, 0, v___x_2111_);
lean_ctor_set(v___x_2138_, 1, v___x_2135_);
lean_ctor_set(v___x_2138_, 2, v___x_2137_);
lean_ctor_set(v___x_2138_, 3, v___x_2116_);
v___x_2139_ = l_Lean_Syntax_node2(v___x_2111_, v___x_2132_, v___x_2134_, v___x_2138_);
v___x_2140_ = l_Lean_Syntax_node1(v___x_2111_, v___x_2119_, v_a_2102_);
v___x_2141_ = l_Lean_Syntax_node2(v___x_2111_, v___x_2112_, v___x_2139_, v___x_2140_);
v___x_2142_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__72));
v___x_2143_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2143_, 0, v___x_2111_);
lean_ctor_set(v___x_2143_, 1, v___x_2142_);
v___x_2144_ = l_Lean_Syntax_node3(v___x_2111_, v___x_2120_, v___x_2131_, v___x_2141_, v___x_2143_);
v___x_2145_ = l_Lean_Syntax_node1(v___x_2111_, v___x_2119_, v___x_2144_);
v___x_2146_ = l_Lean_Syntax_node2(v___x_2111_, v___x_2112_, v___x_2118_, v___x_2145_);
if (v_isShared_2106_ == 0)
{
lean_ctor_set(v___x_2105_, 0, v___x_2146_);
v___x_2148_ = v___x_2105_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2149_; 
v_reuseFailAlloc_2149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2149_, 0, v___x_2146_);
lean_ctor_set(v_reuseFailAlloc_2149_, 1, v_a_2103_);
v___x_2148_ = v_reuseFailAlloc_2149_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
return v___x_2148_;
}
}
}
}
case 8:
{
lean_object* v_presentation_2151_; 
v_presentation_2151_ = lean_ctor_get(v_x_1711_, 0);
lean_inc_ref(v_presentation_2151_);
lean_dec_ref_known(v_x_1711_, 1);
if (lean_obj_tag(v_presentation_2151_) == 0)
{
lean_object* v_val_2152_; lean_object* v___x_2153_; lean_object* v_a_2154_; lean_object* v_a_2155_; lean_object* v___x_2157_; uint8_t v_isShared_2158_; uint8_t v_isSharedCheck_2202_; 
v_val_2152_ = lean_ctor_get(v_presentation_2151_, 0);
lean_inc(v_val_2152_);
lean_dec_ref_known(v_presentation_2151_, 1);
v___x_2153_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber(v_val_2152_, v_a_1712_, v_a_1713_);
v_a_2154_ = lean_ctor_get(v___x_2153_, 0);
v_a_2155_ = lean_ctor_get(v___x_2153_, 1);
v_isSharedCheck_2202_ = !lean_is_exclusive(v___x_2153_);
if (v_isSharedCheck_2202_ == 0)
{
v___x_2157_ = v___x_2153_;
v_isShared_2158_ = v_isSharedCheck_2202_;
goto v_resetjp_2156_;
}
else
{
lean_inc(v_a_2155_);
lean_inc(v_a_2154_);
lean_dec(v___x_2153_);
v___x_2157_ = lean_box(0);
v_isShared_2158_ = v_isSharedCheck_2202_;
goto v_resetjp_2156_;
}
v_resetjp_2156_:
{
lean_object* v_quotContext_2159_; lean_object* v_currMacroScope_2160_; lean_object* v_ref_2161_; uint8_t v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2200_; 
v_quotContext_2159_ = lean_ctor_get(v_a_1712_, 1);
v_currMacroScope_2160_ = lean_ctor_get(v_a_1712_, 2);
v_ref_2161_ = lean_ctor_get(v_a_1712_, 5);
v___x_2162_ = 0;
v___x_2163_ = l_Lean_SourceInfo_fromRef(v_ref_2161_, v___x_2162_);
v___x_2164_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4));
v___x_2165_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__101, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__101_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__101);
v___x_2166_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__103));
lean_inc_n(v_currMacroScope_2160_, 3);
lean_inc_n(v_quotContext_2159_, 3);
v___x_2167_ = l_Lean_addMacroScope(v_quotContext_2159_, v___x_2166_, v_currMacroScope_2160_);
v___x_2168_ = lean_box(0);
v___x_2169_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__107));
lean_inc_n(v___x_2163_, 13);
v___x_2170_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2170_, 0, v___x_2163_);
lean_ctor_set(v___x_2170_, 1, v___x_2165_);
lean_ctor_set(v___x_2170_, 2, v___x_2167_);
lean_ctor_set(v___x_2170_, 3, v___x_2169_);
v___x_2171_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15));
v___x_2172_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__42));
v___x_2173_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__44));
v___x_2174_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__45));
v___x_2175_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2175_, 0, v___x_2163_);
lean_ctor_set(v___x_2175_, 1, v___x_2174_);
v___x_2176_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__47));
v___x_2177_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__49, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__49_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__49);
v___x_2178_ = lean_box(0);
v___x_2179_ = l_Lean_addMacroScope(v_quotContext_2159_, v___x_2178_, v_currMacroScope_2160_);
v___x_2180_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__65));
v___x_2181_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2181_, 0, v___x_2163_);
lean_ctor_set(v___x_2181_, 1, v___x_2177_);
lean_ctor_set(v___x_2181_, 2, v___x_2179_);
lean_ctor_set(v___x_2181_, 3, v___x_2180_);
v___x_2182_ = l_Lean_Syntax_node1(v___x_2163_, v___x_2176_, v___x_2181_);
v___x_2183_ = l_Lean_Syntax_node2(v___x_2163_, v___x_2173_, v___x_2175_, v___x_2182_);
v___x_2184_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__67));
v___x_2185_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__68));
v___x_2186_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2186_, 0, v___x_2163_);
lean_ctor_set(v___x_2186_, 1, v___x_2185_);
v___x_2187_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__70, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__70_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__70);
v___x_2188_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__71));
v___x_2189_ = l_Lean_addMacroScope(v_quotContext_2159_, v___x_2188_, v_currMacroScope_2160_);
v___x_2190_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2190_, 0, v___x_2163_);
lean_ctor_set(v___x_2190_, 1, v___x_2187_);
lean_ctor_set(v___x_2190_, 2, v___x_2189_);
lean_ctor_set(v___x_2190_, 3, v___x_2168_);
v___x_2191_ = l_Lean_Syntax_node2(v___x_2163_, v___x_2184_, v___x_2186_, v___x_2190_);
v___x_2192_ = l_Lean_Syntax_node1(v___x_2163_, v___x_2171_, v_a_2154_);
v___x_2193_ = l_Lean_Syntax_node2(v___x_2163_, v___x_2164_, v___x_2191_, v___x_2192_);
v___x_2194_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__72));
v___x_2195_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2195_, 0, v___x_2163_);
lean_ctor_set(v___x_2195_, 1, v___x_2194_);
v___x_2196_ = l_Lean_Syntax_node3(v___x_2163_, v___x_2172_, v___x_2183_, v___x_2193_, v___x_2195_);
v___x_2197_ = l_Lean_Syntax_node1(v___x_2163_, v___x_2171_, v___x_2196_);
v___x_2198_ = l_Lean_Syntax_node2(v___x_2163_, v___x_2164_, v___x_2170_, v___x_2197_);
if (v_isShared_2158_ == 0)
{
lean_ctor_set(v___x_2157_, 0, v___x_2198_);
v___x_2200_ = v___x_2157_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2201_; 
v_reuseFailAlloc_2201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2201_, 0, v___x_2198_);
lean_ctor_set(v_reuseFailAlloc_2201_, 1, v_a_2155_);
v___x_2200_ = v_reuseFailAlloc_2201_;
goto v_reusejp_2199_;
}
v_reusejp_2199_:
{
return v___x_2200_;
}
}
}
else
{
lean_object* v_val_2203_; uint8_t v___x_2204_; lean_object* v___x_2205_; lean_object* v_a_2206_; lean_object* v_a_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2254_; 
v_val_2203_ = lean_ctor_get(v_presentation_2151_, 0);
lean_inc(v_val_2203_);
lean_dec_ref_known(v_presentation_2151_, 1);
v___x_2204_ = lean_unbox(v_val_2203_);
lean_dec(v_val_2203_);
v___x_2205_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertText(v___x_2204_, v_a_1712_, v_a_1713_);
v_a_2206_ = lean_ctor_get(v___x_2205_, 0);
v_a_2207_ = lean_ctor_get(v___x_2205_, 1);
v_isSharedCheck_2254_ = !lean_is_exclusive(v___x_2205_);
if (v_isSharedCheck_2254_ == 0)
{
v___x_2209_ = v___x_2205_;
v_isShared_2210_ = v_isSharedCheck_2254_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_a_2207_);
lean_inc(v_a_2206_);
lean_dec(v___x_2205_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2254_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
lean_object* v_quotContext_2211_; lean_object* v_currMacroScope_2212_; lean_object* v_ref_2213_; uint8_t v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2252_; 
v_quotContext_2211_ = lean_ctor_get(v_a_1712_, 1);
v_currMacroScope_2212_ = lean_ctor_get(v_a_1712_, 2);
v_ref_2213_ = lean_ctor_get(v_a_1712_, 5);
v___x_2214_ = 0;
v___x_2215_ = l_Lean_SourceInfo_fromRef(v_ref_2213_, v___x_2214_);
v___x_2216_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4));
v___x_2217_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__101, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__101_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__101);
v___x_2218_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__103));
lean_inc_n(v_currMacroScope_2212_, 3);
lean_inc_n(v_quotContext_2211_, 3);
v___x_2219_ = l_Lean_addMacroScope(v_quotContext_2211_, v___x_2218_, v_currMacroScope_2212_);
v___x_2220_ = lean_box(0);
v___x_2221_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__107));
lean_inc_n(v___x_2215_, 13);
v___x_2222_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2222_, 0, v___x_2215_);
lean_ctor_set(v___x_2222_, 1, v___x_2217_);
lean_ctor_set(v___x_2222_, 2, v___x_2219_);
lean_ctor_set(v___x_2222_, 3, v___x_2221_);
v___x_2223_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15));
v___x_2224_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__42));
v___x_2225_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__44));
v___x_2226_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__45));
v___x_2227_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2227_, 0, v___x_2215_);
lean_ctor_set(v___x_2227_, 1, v___x_2226_);
v___x_2228_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__47));
v___x_2229_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__49, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__49_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__49);
v___x_2230_ = lean_box(0);
v___x_2231_ = l_Lean_addMacroScope(v_quotContext_2211_, v___x_2230_, v_currMacroScope_2212_);
v___x_2232_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__65));
v___x_2233_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2233_, 0, v___x_2215_);
lean_ctor_set(v___x_2233_, 1, v___x_2229_);
lean_ctor_set(v___x_2233_, 2, v___x_2231_);
lean_ctor_set(v___x_2233_, 3, v___x_2232_);
v___x_2234_ = l_Lean_Syntax_node1(v___x_2215_, v___x_2228_, v___x_2233_);
v___x_2235_ = l_Lean_Syntax_node2(v___x_2215_, v___x_2225_, v___x_2227_, v___x_2234_);
v___x_2236_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__67));
v___x_2237_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__68));
v___x_2238_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2238_, 0, v___x_2215_);
lean_ctor_set(v___x_2238_, 1, v___x_2237_);
v___x_2239_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__74, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__74_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__74);
v___x_2240_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__75));
v___x_2241_ = l_Lean_addMacroScope(v_quotContext_2211_, v___x_2240_, v_currMacroScope_2212_);
v___x_2242_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2242_, 0, v___x_2215_);
lean_ctor_set(v___x_2242_, 1, v___x_2239_);
lean_ctor_set(v___x_2242_, 2, v___x_2241_);
lean_ctor_set(v___x_2242_, 3, v___x_2220_);
v___x_2243_ = l_Lean_Syntax_node2(v___x_2215_, v___x_2236_, v___x_2238_, v___x_2242_);
v___x_2244_ = l_Lean_Syntax_node1(v___x_2215_, v___x_2223_, v_a_2206_);
v___x_2245_ = l_Lean_Syntax_node2(v___x_2215_, v___x_2216_, v___x_2243_, v___x_2244_);
v___x_2246_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__72));
v___x_2247_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2247_, 0, v___x_2215_);
lean_ctor_set(v___x_2247_, 1, v___x_2246_);
v___x_2248_ = l_Lean_Syntax_node3(v___x_2215_, v___x_2224_, v___x_2235_, v___x_2245_, v___x_2247_);
v___x_2249_ = l_Lean_Syntax_node1(v___x_2215_, v___x_2223_, v___x_2248_);
v___x_2250_ = l_Lean_Syntax_node2(v___x_2215_, v___x_2216_, v___x_2222_, v___x_2249_);
if (v_isShared_2210_ == 0)
{
lean_ctor_set(v___x_2209_, 0, v___x_2250_);
v___x_2252_ = v___x_2209_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v___x_2250_);
lean_ctor_set(v_reuseFailAlloc_2253_, 1, v_a_2207_);
v___x_2252_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2251_;
}
v_reusejp_2251_:
{
return v___x_2252_;
}
}
}
}
case 9:
{
lean_object* v_presentation_2255_; lean_object* v___x_2256_; lean_object* v_a_2257_; lean_object* v_a_2258_; lean_object* v___x_2260_; uint8_t v_isShared_2261_; uint8_t v_isSharedCheck_2279_; 
v_presentation_2255_ = lean_ctor_get(v_x_1711_, 0);
lean_inc(v_presentation_2255_);
lean_dec_ref_known(v_x_1711_, 1);
v___x_2256_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear(v_presentation_2255_, v_a_1712_, v_a_1713_);
v_a_2257_ = lean_ctor_get(v___x_2256_, 0);
v_a_2258_ = lean_ctor_get(v___x_2256_, 1);
v_isSharedCheck_2279_ = !lean_is_exclusive(v___x_2256_);
if (v_isSharedCheck_2279_ == 0)
{
v___x_2260_ = v___x_2256_;
v_isShared_2261_ = v_isSharedCheck_2279_;
goto v_resetjp_2259_;
}
else
{
lean_inc(v_a_2258_);
lean_inc(v_a_2257_);
lean_dec(v___x_2256_);
v___x_2260_ = lean_box(0);
v_isShared_2261_ = v_isSharedCheck_2279_;
goto v_resetjp_2259_;
}
v_resetjp_2259_:
{
lean_object* v_quotContext_2262_; lean_object* v_currMacroScope_2263_; lean_object* v_ref_2264_; uint8_t v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2277_; 
v_quotContext_2262_ = lean_ctor_get(v_a_1712_, 1);
v_currMacroScope_2263_ = lean_ctor_get(v_a_1712_, 2);
v_ref_2264_ = lean_ctor_get(v_a_1712_, 5);
v___x_2265_ = 0;
v___x_2266_ = l_Lean_SourceInfo_fromRef(v_ref_2264_, v___x_2265_);
v___x_2267_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4));
v___x_2268_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__109, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__109_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__109);
v___x_2269_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__111));
lean_inc(v_currMacroScope_2263_);
lean_inc(v_quotContext_2262_);
v___x_2270_ = l_Lean_addMacroScope(v_quotContext_2262_, v___x_2269_, v_currMacroScope_2263_);
v___x_2271_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__115));
lean_inc_n(v___x_2266_, 2);
v___x_2272_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2272_, 0, v___x_2266_);
lean_ctor_set(v___x_2272_, 1, v___x_2268_);
lean_ctor_set(v___x_2272_, 2, v___x_2270_);
lean_ctor_set(v___x_2272_, 3, v___x_2271_);
v___x_2273_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15));
v___x_2274_ = l_Lean_Syntax_node1(v___x_2266_, v___x_2273_, v_a_2257_);
v___x_2275_ = l_Lean_Syntax_node2(v___x_2266_, v___x_2267_, v___x_2272_, v___x_2274_);
if (v_isShared_2261_ == 0)
{
lean_ctor_set(v___x_2260_, 0, v___x_2275_);
v___x_2277_ = v___x_2260_;
goto v_reusejp_2276_;
}
else
{
lean_object* v_reuseFailAlloc_2278_; 
v_reuseFailAlloc_2278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2278_, 0, v___x_2275_);
lean_ctor_set(v_reuseFailAlloc_2278_, 1, v_a_2258_);
v___x_2277_ = v_reuseFailAlloc_2278_;
goto v_reusejp_2276_;
}
v_reusejp_2276_:
{
return v___x_2277_;
}
}
}
case 10:
{
lean_object* v_presentation_2280_; lean_object* v___x_2281_; lean_object* v_a_2282_; lean_object* v_a_2283_; lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2304_; 
v_presentation_2280_ = lean_ctor_get(v_x_1711_, 0);
lean_inc(v_presentation_2280_);
lean_dec_ref_known(v_x_1711_, 1);
v___x_2281_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber(v_presentation_2280_, v_a_1712_, v_a_1713_);
v_a_2282_ = lean_ctor_get(v___x_2281_, 0);
v_a_2283_ = lean_ctor_get(v___x_2281_, 1);
v_isSharedCheck_2304_ = !lean_is_exclusive(v___x_2281_);
if (v_isSharedCheck_2304_ == 0)
{
v___x_2285_ = v___x_2281_;
v_isShared_2286_ = v_isSharedCheck_2304_;
goto v_resetjp_2284_;
}
else
{
lean_inc(v_a_2283_);
lean_inc(v_a_2282_);
lean_dec(v___x_2281_);
v___x_2285_ = lean_box(0);
v_isShared_2286_ = v_isSharedCheck_2304_;
goto v_resetjp_2284_;
}
v_resetjp_2284_:
{
lean_object* v_quotContext_2287_; lean_object* v_currMacroScope_2288_; lean_object* v_ref_2289_; uint8_t v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2302_; 
v_quotContext_2287_ = lean_ctor_get(v_a_1712_, 1);
v_currMacroScope_2288_ = lean_ctor_get(v_a_1712_, 2);
v_ref_2289_ = lean_ctor_get(v_a_1712_, 5);
v___x_2290_ = 0;
v___x_2291_ = l_Lean_SourceInfo_fromRef(v_ref_2289_, v___x_2290_);
v___x_2292_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4));
v___x_2293_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__117, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__117_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__117);
v___x_2294_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__119));
lean_inc(v_currMacroScope_2288_);
lean_inc(v_quotContext_2287_);
v___x_2295_ = l_Lean_addMacroScope(v_quotContext_2287_, v___x_2294_, v_currMacroScope_2288_);
v___x_2296_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__123));
lean_inc_n(v___x_2291_, 2);
v___x_2297_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2297_, 0, v___x_2291_);
lean_ctor_set(v___x_2297_, 1, v___x_2293_);
lean_ctor_set(v___x_2297_, 2, v___x_2295_);
lean_ctor_set(v___x_2297_, 3, v___x_2296_);
v___x_2298_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15));
v___x_2299_ = l_Lean_Syntax_node1(v___x_2291_, v___x_2298_, v_a_2282_);
v___x_2300_ = l_Lean_Syntax_node2(v___x_2291_, v___x_2292_, v___x_2297_, v___x_2299_);
if (v_isShared_2286_ == 0)
{
lean_ctor_set(v___x_2285_, 0, v___x_2300_);
v___x_2302_ = v___x_2285_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2303_; 
v_reuseFailAlloc_2303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2303_, 0, v___x_2300_);
lean_ctor_set(v_reuseFailAlloc_2303_, 1, v_a_2283_);
v___x_2302_ = v_reuseFailAlloc_2303_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
return v___x_2302_;
}
}
}
case 11:
{
lean_object* v_presentation_2305_; lean_object* v___x_2306_; lean_object* v_a_2307_; lean_object* v_a_2308_; lean_object* v___x_2310_; uint8_t v_isShared_2311_; uint8_t v_isSharedCheck_2329_; 
v_presentation_2305_ = lean_ctor_get(v_x_1711_, 0);
lean_inc(v_presentation_2305_);
lean_dec_ref_known(v_x_1711_, 1);
v___x_2306_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber(v_presentation_2305_, v_a_1712_, v_a_1713_);
v_a_2307_ = lean_ctor_get(v___x_2306_, 0);
v_a_2308_ = lean_ctor_get(v___x_2306_, 1);
v_isSharedCheck_2329_ = !lean_is_exclusive(v___x_2306_);
if (v_isSharedCheck_2329_ == 0)
{
v___x_2310_ = v___x_2306_;
v_isShared_2311_ = v_isSharedCheck_2329_;
goto v_resetjp_2309_;
}
else
{
lean_inc(v_a_2308_);
lean_inc(v_a_2307_);
lean_dec(v___x_2306_);
v___x_2310_ = lean_box(0);
v_isShared_2311_ = v_isSharedCheck_2329_;
goto v_resetjp_2309_;
}
v_resetjp_2309_:
{
lean_object* v_quotContext_2312_; lean_object* v_currMacroScope_2313_; lean_object* v_ref_2314_; uint8_t v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2327_; 
v_quotContext_2312_ = lean_ctor_get(v_a_1712_, 1);
v_currMacroScope_2313_ = lean_ctor_get(v_a_1712_, 2);
v_ref_2314_ = lean_ctor_get(v_a_1712_, 5);
v___x_2315_ = 0;
v___x_2316_ = l_Lean_SourceInfo_fromRef(v_ref_2314_, v___x_2315_);
v___x_2317_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4));
v___x_2318_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__125, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__125_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__125);
v___x_2319_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__127));
lean_inc(v_currMacroScope_2313_);
lean_inc(v_quotContext_2312_);
v___x_2320_ = l_Lean_addMacroScope(v_quotContext_2312_, v___x_2319_, v_currMacroScope_2313_);
v___x_2321_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__131));
lean_inc_n(v___x_2316_, 2);
v___x_2322_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2322_, 0, v___x_2316_);
lean_ctor_set(v___x_2322_, 1, v___x_2318_);
lean_ctor_set(v___x_2322_, 2, v___x_2320_);
lean_ctor_set(v___x_2322_, 3, v___x_2321_);
v___x_2323_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15));
v___x_2324_ = l_Lean_Syntax_node1(v___x_2316_, v___x_2323_, v_a_2307_);
v___x_2325_ = l_Lean_Syntax_node2(v___x_2316_, v___x_2317_, v___x_2322_, v___x_2324_);
if (v_isShared_2311_ == 0)
{
lean_ctor_set(v___x_2310_, 0, v___x_2325_);
v___x_2327_ = v___x_2310_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2328_; 
v_reuseFailAlloc_2328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2328_, 0, v___x_2325_);
lean_ctor_set(v_reuseFailAlloc_2328_, 1, v_a_2308_);
v___x_2327_ = v_reuseFailAlloc_2328_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
return v___x_2327_;
}
}
}
case 12:
{
uint8_t v_presentation_2330_; lean_object* v___x_2331_; lean_object* v_a_2332_; lean_object* v_a_2333_; lean_object* v___x_2335_; uint8_t v_isShared_2336_; uint8_t v_isSharedCheck_2354_; 
v_presentation_2330_ = lean_ctor_get_uint8(v_x_1711_, 0);
lean_dec_ref_known(v_x_1711_, 0);
v___x_2331_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertText(v_presentation_2330_, v_a_1712_, v_a_1713_);
v_a_2332_ = lean_ctor_get(v___x_2331_, 0);
v_a_2333_ = lean_ctor_get(v___x_2331_, 1);
v_isSharedCheck_2354_ = !lean_is_exclusive(v___x_2331_);
if (v_isSharedCheck_2354_ == 0)
{
v___x_2335_ = v___x_2331_;
v_isShared_2336_ = v_isSharedCheck_2354_;
goto v_resetjp_2334_;
}
else
{
lean_inc(v_a_2333_);
lean_inc(v_a_2332_);
lean_dec(v___x_2331_);
v___x_2335_ = lean_box(0);
v_isShared_2336_ = v_isSharedCheck_2354_;
goto v_resetjp_2334_;
}
v_resetjp_2334_:
{
lean_object* v_quotContext_2337_; lean_object* v_currMacroScope_2338_; lean_object* v_ref_2339_; uint8_t v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2352_; 
v_quotContext_2337_ = lean_ctor_get(v_a_1712_, 1);
v_currMacroScope_2338_ = lean_ctor_get(v_a_1712_, 2);
v_ref_2339_ = lean_ctor_get(v_a_1712_, 5);
v___x_2340_ = 0;
v___x_2341_ = l_Lean_SourceInfo_fromRef(v_ref_2339_, v___x_2340_);
v___x_2342_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4));
v___x_2343_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__133, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__133_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__133);
v___x_2344_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__135));
lean_inc(v_currMacroScope_2338_);
lean_inc(v_quotContext_2337_);
v___x_2345_ = l_Lean_addMacroScope(v_quotContext_2337_, v___x_2344_, v_currMacroScope_2338_);
v___x_2346_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__139));
lean_inc_n(v___x_2341_, 2);
v___x_2347_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2347_, 0, v___x_2341_);
lean_ctor_set(v___x_2347_, 1, v___x_2343_);
lean_ctor_set(v___x_2347_, 2, v___x_2345_);
lean_ctor_set(v___x_2347_, 3, v___x_2346_);
v___x_2348_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15));
v___x_2349_ = l_Lean_Syntax_node1(v___x_2341_, v___x_2348_, v_a_2332_);
v___x_2350_ = l_Lean_Syntax_node2(v___x_2341_, v___x_2342_, v___x_2347_, v___x_2349_);
if (v_isShared_2336_ == 0)
{
lean_ctor_set(v___x_2335_, 0, v___x_2350_);
v___x_2352_ = v___x_2335_;
goto v_reusejp_2351_;
}
else
{
lean_object* v_reuseFailAlloc_2353_; 
v_reuseFailAlloc_2353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2353_, 0, v___x_2350_);
lean_ctor_set(v_reuseFailAlloc_2353_, 1, v_a_2333_);
v___x_2352_ = v_reuseFailAlloc_2353_;
goto v_reusejp_2351_;
}
v_reusejp_2351_:
{
return v___x_2352_;
}
}
}
case 13:
{
lean_object* v_presentation_2355_; 
v_presentation_2355_ = lean_ctor_get(v_x_1711_, 0);
lean_inc_ref(v_presentation_2355_);
lean_dec_ref_known(v_x_1711_, 1);
if (lean_obj_tag(v_presentation_2355_) == 0)
{
lean_object* v_val_2356_; lean_object* v___x_2357_; lean_object* v_a_2358_; lean_object* v_a_2359_; lean_object* v___x_2361_; uint8_t v_isShared_2362_; uint8_t v_isSharedCheck_2406_; 
v_val_2356_ = lean_ctor_get(v_presentation_2355_, 0);
lean_inc(v_val_2356_);
lean_dec_ref_known(v_presentation_2355_, 1);
v___x_2357_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber(v_val_2356_, v_a_1712_, v_a_1713_);
v_a_2358_ = lean_ctor_get(v___x_2357_, 0);
v_a_2359_ = lean_ctor_get(v___x_2357_, 1);
v_isSharedCheck_2406_ = !lean_is_exclusive(v___x_2357_);
if (v_isSharedCheck_2406_ == 0)
{
v___x_2361_ = v___x_2357_;
v_isShared_2362_ = v_isSharedCheck_2406_;
goto v_resetjp_2360_;
}
else
{
lean_inc(v_a_2359_);
lean_inc(v_a_2358_);
lean_dec(v___x_2357_);
v___x_2361_ = lean_box(0);
v_isShared_2362_ = v_isSharedCheck_2406_;
goto v_resetjp_2360_;
}
v_resetjp_2360_:
{
lean_object* v_quotContext_2363_; lean_object* v_currMacroScope_2364_; lean_object* v_ref_2365_; uint8_t v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2404_; 
v_quotContext_2363_ = lean_ctor_get(v_a_1712_, 1);
v_currMacroScope_2364_ = lean_ctor_get(v_a_1712_, 2);
v_ref_2365_ = lean_ctor_get(v_a_1712_, 5);
v___x_2366_ = 0;
v___x_2367_ = l_Lean_SourceInfo_fromRef(v_ref_2365_, v___x_2366_);
v___x_2368_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4));
v___x_2369_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__141, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__141_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__141);
v___x_2370_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__143));
lean_inc_n(v_currMacroScope_2364_, 3);
lean_inc_n(v_quotContext_2363_, 3);
v___x_2371_ = l_Lean_addMacroScope(v_quotContext_2363_, v___x_2370_, v_currMacroScope_2364_);
v___x_2372_ = lean_box(0);
v___x_2373_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__147));
lean_inc_n(v___x_2367_, 13);
v___x_2374_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2374_, 0, v___x_2367_);
lean_ctor_set(v___x_2374_, 1, v___x_2369_);
lean_ctor_set(v___x_2374_, 2, v___x_2371_);
lean_ctor_set(v___x_2374_, 3, v___x_2373_);
v___x_2375_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15));
v___x_2376_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__42));
v___x_2377_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__44));
v___x_2378_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__45));
v___x_2379_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2379_, 0, v___x_2367_);
lean_ctor_set(v___x_2379_, 1, v___x_2378_);
v___x_2380_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__47));
v___x_2381_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__49, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__49_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__49);
v___x_2382_ = lean_box(0);
v___x_2383_ = l_Lean_addMacroScope(v_quotContext_2363_, v___x_2382_, v_currMacroScope_2364_);
v___x_2384_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__65));
v___x_2385_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2385_, 0, v___x_2367_);
lean_ctor_set(v___x_2385_, 1, v___x_2381_);
lean_ctor_set(v___x_2385_, 2, v___x_2383_);
lean_ctor_set(v___x_2385_, 3, v___x_2384_);
v___x_2386_ = l_Lean_Syntax_node1(v___x_2367_, v___x_2380_, v___x_2385_);
v___x_2387_ = l_Lean_Syntax_node2(v___x_2367_, v___x_2377_, v___x_2379_, v___x_2386_);
v___x_2388_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__67));
v___x_2389_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__68));
v___x_2390_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2390_, 0, v___x_2367_);
lean_ctor_set(v___x_2390_, 1, v___x_2389_);
v___x_2391_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__70, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__70_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__70);
v___x_2392_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__71));
v___x_2393_ = l_Lean_addMacroScope(v_quotContext_2363_, v___x_2392_, v_currMacroScope_2364_);
v___x_2394_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2394_, 0, v___x_2367_);
lean_ctor_set(v___x_2394_, 1, v___x_2391_);
lean_ctor_set(v___x_2394_, 2, v___x_2393_);
lean_ctor_set(v___x_2394_, 3, v___x_2372_);
v___x_2395_ = l_Lean_Syntax_node2(v___x_2367_, v___x_2388_, v___x_2390_, v___x_2394_);
v___x_2396_ = l_Lean_Syntax_node1(v___x_2367_, v___x_2375_, v_a_2358_);
v___x_2397_ = l_Lean_Syntax_node2(v___x_2367_, v___x_2368_, v___x_2395_, v___x_2396_);
v___x_2398_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__72));
v___x_2399_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2399_, 0, v___x_2367_);
lean_ctor_set(v___x_2399_, 1, v___x_2398_);
v___x_2400_ = l_Lean_Syntax_node3(v___x_2367_, v___x_2376_, v___x_2387_, v___x_2397_, v___x_2399_);
v___x_2401_ = l_Lean_Syntax_node1(v___x_2367_, v___x_2375_, v___x_2400_);
v___x_2402_ = l_Lean_Syntax_node2(v___x_2367_, v___x_2368_, v___x_2374_, v___x_2401_);
if (v_isShared_2362_ == 0)
{
lean_ctor_set(v___x_2361_, 0, v___x_2402_);
v___x_2404_ = v___x_2361_;
goto v_reusejp_2403_;
}
else
{
lean_object* v_reuseFailAlloc_2405_; 
v_reuseFailAlloc_2405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2405_, 0, v___x_2402_);
lean_ctor_set(v_reuseFailAlloc_2405_, 1, v_a_2359_);
v___x_2404_ = v_reuseFailAlloc_2405_;
goto v_reusejp_2403_;
}
v_reusejp_2403_:
{
return v___x_2404_;
}
}
}
else
{
lean_object* v_val_2407_; uint8_t v___x_2408_; lean_object* v___x_2409_; lean_object* v_a_2410_; lean_object* v_a_2411_; lean_object* v___x_2413_; uint8_t v_isShared_2414_; uint8_t v_isSharedCheck_2458_; 
v_val_2407_ = lean_ctor_get(v_presentation_2355_, 0);
lean_inc(v_val_2407_);
lean_dec_ref_known(v_presentation_2355_, 1);
v___x_2408_ = lean_unbox(v_val_2407_);
lean_dec(v_val_2407_);
v___x_2409_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertText(v___x_2408_, v_a_1712_, v_a_1713_);
v_a_2410_ = lean_ctor_get(v___x_2409_, 0);
v_a_2411_ = lean_ctor_get(v___x_2409_, 1);
v_isSharedCheck_2458_ = !lean_is_exclusive(v___x_2409_);
if (v_isSharedCheck_2458_ == 0)
{
v___x_2413_ = v___x_2409_;
v_isShared_2414_ = v_isSharedCheck_2458_;
goto v_resetjp_2412_;
}
else
{
lean_inc(v_a_2411_);
lean_inc(v_a_2410_);
lean_dec(v___x_2409_);
v___x_2413_ = lean_box(0);
v_isShared_2414_ = v_isSharedCheck_2458_;
goto v_resetjp_2412_;
}
v_resetjp_2412_:
{
lean_object* v_quotContext_2415_; lean_object* v_currMacroScope_2416_; lean_object* v_ref_2417_; uint8_t v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2456_; 
v_quotContext_2415_ = lean_ctor_get(v_a_1712_, 1);
v_currMacroScope_2416_ = lean_ctor_get(v_a_1712_, 2);
v_ref_2417_ = lean_ctor_get(v_a_1712_, 5);
v___x_2418_ = 0;
v___x_2419_ = l_Lean_SourceInfo_fromRef(v_ref_2417_, v___x_2418_);
v___x_2420_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4));
v___x_2421_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__141, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__141_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__141);
v___x_2422_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__143));
lean_inc_n(v_currMacroScope_2416_, 3);
lean_inc_n(v_quotContext_2415_, 3);
v___x_2423_ = l_Lean_addMacroScope(v_quotContext_2415_, v___x_2422_, v_currMacroScope_2416_);
v___x_2424_ = lean_box(0);
v___x_2425_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__147));
lean_inc_n(v___x_2419_, 13);
v___x_2426_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2426_, 0, v___x_2419_);
lean_ctor_set(v___x_2426_, 1, v___x_2421_);
lean_ctor_set(v___x_2426_, 2, v___x_2423_);
lean_ctor_set(v___x_2426_, 3, v___x_2425_);
v___x_2427_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15));
v___x_2428_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__42));
v___x_2429_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__44));
v___x_2430_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__45));
v___x_2431_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2431_, 0, v___x_2419_);
lean_ctor_set(v___x_2431_, 1, v___x_2430_);
v___x_2432_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__47));
v___x_2433_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__49, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__49_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__49);
v___x_2434_ = lean_box(0);
v___x_2435_ = l_Lean_addMacroScope(v_quotContext_2415_, v___x_2434_, v_currMacroScope_2416_);
v___x_2436_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__65));
v___x_2437_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2437_, 0, v___x_2419_);
lean_ctor_set(v___x_2437_, 1, v___x_2433_);
lean_ctor_set(v___x_2437_, 2, v___x_2435_);
lean_ctor_set(v___x_2437_, 3, v___x_2436_);
v___x_2438_ = l_Lean_Syntax_node1(v___x_2419_, v___x_2432_, v___x_2437_);
v___x_2439_ = l_Lean_Syntax_node2(v___x_2419_, v___x_2429_, v___x_2431_, v___x_2438_);
v___x_2440_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__67));
v___x_2441_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__68));
v___x_2442_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2442_, 0, v___x_2419_);
lean_ctor_set(v___x_2442_, 1, v___x_2441_);
v___x_2443_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__74, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__74_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__74);
v___x_2444_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__75));
v___x_2445_ = l_Lean_addMacroScope(v_quotContext_2415_, v___x_2444_, v_currMacroScope_2416_);
v___x_2446_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2446_, 0, v___x_2419_);
lean_ctor_set(v___x_2446_, 1, v___x_2443_);
lean_ctor_set(v___x_2446_, 2, v___x_2445_);
lean_ctor_set(v___x_2446_, 3, v___x_2424_);
v___x_2447_ = l_Lean_Syntax_node2(v___x_2419_, v___x_2440_, v___x_2442_, v___x_2446_);
v___x_2448_ = l_Lean_Syntax_node1(v___x_2419_, v___x_2427_, v_a_2410_);
v___x_2449_ = l_Lean_Syntax_node2(v___x_2419_, v___x_2420_, v___x_2447_, v___x_2448_);
v___x_2450_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__72));
v___x_2451_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2451_, 0, v___x_2419_);
lean_ctor_set(v___x_2451_, 1, v___x_2450_);
v___x_2452_ = l_Lean_Syntax_node3(v___x_2419_, v___x_2428_, v___x_2439_, v___x_2449_, v___x_2451_);
v___x_2453_ = l_Lean_Syntax_node1(v___x_2419_, v___x_2427_, v___x_2452_);
v___x_2454_ = l_Lean_Syntax_node2(v___x_2419_, v___x_2420_, v___x_2426_, v___x_2453_);
if (v_isShared_2414_ == 0)
{
lean_ctor_set(v___x_2413_, 0, v___x_2454_);
v___x_2456_ = v___x_2413_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v___x_2454_);
lean_ctor_set(v_reuseFailAlloc_2457_, 1, v_a_2411_);
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
case 14:
{
lean_object* v_presentation_2459_; 
v_presentation_2459_ = lean_ctor_get(v_x_1711_, 0);
lean_inc_ref(v_presentation_2459_);
lean_dec_ref_known(v_x_1711_, 1);
if (lean_obj_tag(v_presentation_2459_) == 0)
{
lean_object* v_val_2460_; lean_object* v___x_2461_; lean_object* v_a_2462_; lean_object* v_a_2463_; lean_object* v___x_2465_; uint8_t v_isShared_2466_; uint8_t v_isSharedCheck_2510_; 
v_val_2460_ = lean_ctor_get(v_presentation_2459_, 0);
lean_inc(v_val_2460_);
lean_dec_ref_known(v_presentation_2459_, 1);
v___x_2461_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber(v_val_2460_, v_a_1712_, v_a_1713_);
v_a_2462_ = lean_ctor_get(v___x_2461_, 0);
v_a_2463_ = lean_ctor_get(v___x_2461_, 1);
v_isSharedCheck_2510_ = !lean_is_exclusive(v___x_2461_);
if (v_isSharedCheck_2510_ == 0)
{
v___x_2465_ = v___x_2461_;
v_isShared_2466_ = v_isSharedCheck_2510_;
goto v_resetjp_2464_;
}
else
{
lean_inc(v_a_2463_);
lean_inc(v_a_2462_);
lean_dec(v___x_2461_);
v___x_2465_ = lean_box(0);
v_isShared_2466_ = v_isSharedCheck_2510_;
goto v_resetjp_2464_;
}
v_resetjp_2464_:
{
lean_object* v_quotContext_2467_; lean_object* v_currMacroScope_2468_; lean_object* v_ref_2469_; uint8_t v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2508_; 
v_quotContext_2467_ = lean_ctor_get(v_a_1712_, 1);
v_currMacroScope_2468_ = lean_ctor_get(v_a_1712_, 2);
v_ref_2469_ = lean_ctor_get(v_a_1712_, 5);
v___x_2470_ = 0;
v___x_2471_ = l_Lean_SourceInfo_fromRef(v_ref_2469_, v___x_2470_);
v___x_2472_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4));
v___x_2473_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__149, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__149_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__149);
v___x_2474_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__151));
lean_inc_n(v_currMacroScope_2468_, 3);
lean_inc_n(v_quotContext_2467_, 3);
v___x_2475_ = l_Lean_addMacroScope(v_quotContext_2467_, v___x_2474_, v_currMacroScope_2468_);
v___x_2476_ = lean_box(0);
v___x_2477_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__155));
lean_inc_n(v___x_2471_, 13);
v___x_2478_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2478_, 0, v___x_2471_);
lean_ctor_set(v___x_2478_, 1, v___x_2473_);
lean_ctor_set(v___x_2478_, 2, v___x_2475_);
lean_ctor_set(v___x_2478_, 3, v___x_2477_);
v___x_2479_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15));
v___x_2480_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__42));
v___x_2481_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__44));
v___x_2482_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__45));
v___x_2483_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2483_, 0, v___x_2471_);
lean_ctor_set(v___x_2483_, 1, v___x_2482_);
v___x_2484_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__47));
v___x_2485_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__49, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__49_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__49);
v___x_2486_ = lean_box(0);
v___x_2487_ = l_Lean_addMacroScope(v_quotContext_2467_, v___x_2486_, v_currMacroScope_2468_);
v___x_2488_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__65));
v___x_2489_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2489_, 0, v___x_2471_);
lean_ctor_set(v___x_2489_, 1, v___x_2485_);
lean_ctor_set(v___x_2489_, 2, v___x_2487_);
lean_ctor_set(v___x_2489_, 3, v___x_2488_);
v___x_2490_ = l_Lean_Syntax_node1(v___x_2471_, v___x_2484_, v___x_2489_);
v___x_2491_ = l_Lean_Syntax_node2(v___x_2471_, v___x_2481_, v___x_2483_, v___x_2490_);
v___x_2492_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__67));
v___x_2493_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__68));
v___x_2494_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2494_, 0, v___x_2471_);
lean_ctor_set(v___x_2494_, 1, v___x_2493_);
v___x_2495_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__70, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__70_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__70);
v___x_2496_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__71));
v___x_2497_ = l_Lean_addMacroScope(v_quotContext_2467_, v___x_2496_, v_currMacroScope_2468_);
v___x_2498_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2498_, 0, v___x_2471_);
lean_ctor_set(v___x_2498_, 1, v___x_2495_);
lean_ctor_set(v___x_2498_, 2, v___x_2497_);
lean_ctor_set(v___x_2498_, 3, v___x_2476_);
v___x_2499_ = l_Lean_Syntax_node2(v___x_2471_, v___x_2492_, v___x_2494_, v___x_2498_);
v___x_2500_ = l_Lean_Syntax_node1(v___x_2471_, v___x_2479_, v_a_2462_);
v___x_2501_ = l_Lean_Syntax_node2(v___x_2471_, v___x_2472_, v___x_2499_, v___x_2500_);
v___x_2502_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__72));
v___x_2503_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2503_, 0, v___x_2471_);
lean_ctor_set(v___x_2503_, 1, v___x_2502_);
v___x_2504_ = l_Lean_Syntax_node3(v___x_2471_, v___x_2480_, v___x_2491_, v___x_2501_, v___x_2503_);
v___x_2505_ = l_Lean_Syntax_node1(v___x_2471_, v___x_2479_, v___x_2504_);
v___x_2506_ = l_Lean_Syntax_node2(v___x_2471_, v___x_2472_, v___x_2478_, v___x_2505_);
if (v_isShared_2466_ == 0)
{
lean_ctor_set(v___x_2465_, 0, v___x_2506_);
v___x_2508_ = v___x_2465_;
goto v_reusejp_2507_;
}
else
{
lean_object* v_reuseFailAlloc_2509_; 
v_reuseFailAlloc_2509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2509_, 0, v___x_2506_);
lean_ctor_set(v_reuseFailAlloc_2509_, 1, v_a_2463_);
v___x_2508_ = v_reuseFailAlloc_2509_;
goto v_reusejp_2507_;
}
v_reusejp_2507_:
{
return v___x_2508_;
}
}
}
else
{
lean_object* v_val_2511_; uint8_t v___x_2512_; lean_object* v___x_2513_; lean_object* v_a_2514_; lean_object* v_a_2515_; lean_object* v___x_2517_; uint8_t v_isShared_2518_; uint8_t v_isSharedCheck_2562_; 
v_val_2511_ = lean_ctor_get(v_presentation_2459_, 0);
lean_inc(v_val_2511_);
lean_dec_ref_known(v_presentation_2459_, 1);
v___x_2512_ = lean_unbox(v_val_2511_);
lean_dec(v_val_2511_);
v___x_2513_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertText(v___x_2512_, v_a_1712_, v_a_1713_);
v_a_2514_ = lean_ctor_get(v___x_2513_, 0);
v_a_2515_ = lean_ctor_get(v___x_2513_, 1);
v_isSharedCheck_2562_ = !lean_is_exclusive(v___x_2513_);
if (v_isSharedCheck_2562_ == 0)
{
v___x_2517_ = v___x_2513_;
v_isShared_2518_ = v_isSharedCheck_2562_;
goto v_resetjp_2516_;
}
else
{
lean_inc(v_a_2515_);
lean_inc(v_a_2514_);
lean_dec(v___x_2513_);
v___x_2517_ = lean_box(0);
v_isShared_2518_ = v_isSharedCheck_2562_;
goto v_resetjp_2516_;
}
v_resetjp_2516_:
{
lean_object* v_quotContext_2519_; lean_object* v_currMacroScope_2520_; lean_object* v_ref_2521_; uint8_t v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2560_; 
v_quotContext_2519_ = lean_ctor_get(v_a_1712_, 1);
v_currMacroScope_2520_ = lean_ctor_get(v_a_1712_, 2);
v_ref_2521_ = lean_ctor_get(v_a_1712_, 5);
v___x_2522_ = 0;
v___x_2523_ = l_Lean_SourceInfo_fromRef(v_ref_2521_, v___x_2522_);
v___x_2524_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4));
v___x_2525_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__149, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__149_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__149);
v___x_2526_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__151));
lean_inc_n(v_currMacroScope_2520_, 3);
lean_inc_n(v_quotContext_2519_, 3);
v___x_2527_ = l_Lean_addMacroScope(v_quotContext_2519_, v___x_2526_, v_currMacroScope_2520_);
v___x_2528_ = lean_box(0);
v___x_2529_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__155));
lean_inc_n(v___x_2523_, 13);
v___x_2530_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2530_, 0, v___x_2523_);
lean_ctor_set(v___x_2530_, 1, v___x_2525_);
lean_ctor_set(v___x_2530_, 2, v___x_2527_);
lean_ctor_set(v___x_2530_, 3, v___x_2529_);
v___x_2531_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15));
v___x_2532_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__42));
v___x_2533_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__44));
v___x_2534_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__45));
v___x_2535_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2535_, 0, v___x_2523_);
lean_ctor_set(v___x_2535_, 1, v___x_2534_);
v___x_2536_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__47));
v___x_2537_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__49, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__49_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__49);
v___x_2538_ = lean_box(0);
v___x_2539_ = l_Lean_addMacroScope(v_quotContext_2519_, v___x_2538_, v_currMacroScope_2520_);
v___x_2540_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__65));
v___x_2541_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2541_, 0, v___x_2523_);
lean_ctor_set(v___x_2541_, 1, v___x_2537_);
lean_ctor_set(v___x_2541_, 2, v___x_2539_);
lean_ctor_set(v___x_2541_, 3, v___x_2540_);
v___x_2542_ = l_Lean_Syntax_node1(v___x_2523_, v___x_2536_, v___x_2541_);
v___x_2543_ = l_Lean_Syntax_node2(v___x_2523_, v___x_2533_, v___x_2535_, v___x_2542_);
v___x_2544_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__67));
v___x_2545_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__68));
v___x_2546_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2546_, 0, v___x_2523_);
lean_ctor_set(v___x_2546_, 1, v___x_2545_);
v___x_2547_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__74, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__74_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__74);
v___x_2548_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__75));
v___x_2549_ = l_Lean_addMacroScope(v_quotContext_2519_, v___x_2548_, v_currMacroScope_2520_);
v___x_2550_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2550_, 0, v___x_2523_);
lean_ctor_set(v___x_2550_, 1, v___x_2547_);
lean_ctor_set(v___x_2550_, 2, v___x_2549_);
lean_ctor_set(v___x_2550_, 3, v___x_2528_);
v___x_2551_ = l_Lean_Syntax_node2(v___x_2523_, v___x_2544_, v___x_2546_, v___x_2550_);
v___x_2552_ = l_Lean_Syntax_node1(v___x_2523_, v___x_2531_, v_a_2514_);
v___x_2553_ = l_Lean_Syntax_node2(v___x_2523_, v___x_2524_, v___x_2551_, v___x_2552_);
v___x_2554_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__72));
v___x_2555_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2555_, 0, v___x_2523_);
lean_ctor_set(v___x_2555_, 1, v___x_2554_);
v___x_2556_ = l_Lean_Syntax_node3(v___x_2523_, v___x_2532_, v___x_2543_, v___x_2553_, v___x_2555_);
v___x_2557_ = l_Lean_Syntax_node1(v___x_2523_, v___x_2531_, v___x_2556_);
v___x_2558_ = l_Lean_Syntax_node2(v___x_2523_, v___x_2524_, v___x_2530_, v___x_2557_);
if (v_isShared_2518_ == 0)
{
lean_ctor_set(v___x_2517_, 0, v___x_2558_);
v___x_2560_ = v___x_2517_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v___x_2558_);
lean_ctor_set(v_reuseFailAlloc_2561_, 1, v_a_2515_);
v___x_2560_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
return v___x_2560_;
}
}
}
}
case 15:
{
lean_object* v_presentation_2563_; lean_object* v___x_2564_; lean_object* v_a_2565_; lean_object* v_a_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2587_; 
v_presentation_2563_ = lean_ctor_get(v_x_1711_, 0);
lean_inc(v_presentation_2563_);
lean_dec_ref_known(v_x_1711_, 1);
v___x_2564_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber(v_presentation_2563_, v_a_1712_, v_a_1713_);
v_a_2565_ = lean_ctor_get(v___x_2564_, 0);
v_a_2566_ = lean_ctor_get(v___x_2564_, 1);
v_isSharedCheck_2587_ = !lean_is_exclusive(v___x_2564_);
if (v_isSharedCheck_2587_ == 0)
{
v___x_2568_ = v___x_2564_;
v_isShared_2569_ = v_isSharedCheck_2587_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_a_2566_);
lean_inc(v_a_2565_);
lean_dec(v___x_2564_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2587_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
lean_object* v_quotContext_2570_; lean_object* v_currMacroScope_2571_; lean_object* v_ref_2572_; uint8_t v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2585_; 
v_quotContext_2570_ = lean_ctor_get(v_a_1712_, 1);
v_currMacroScope_2571_ = lean_ctor_get(v_a_1712_, 2);
v_ref_2572_ = lean_ctor_get(v_a_1712_, 5);
v___x_2573_ = 0;
v___x_2574_ = l_Lean_SourceInfo_fromRef(v_ref_2572_, v___x_2573_);
v___x_2575_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4));
v___x_2576_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__157, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__157_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__157);
v___x_2577_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__159));
lean_inc(v_currMacroScope_2571_);
lean_inc(v_quotContext_2570_);
v___x_2578_ = l_Lean_addMacroScope(v_quotContext_2570_, v___x_2577_, v_currMacroScope_2571_);
v___x_2579_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__163));
lean_inc_n(v___x_2574_, 2);
v___x_2580_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2580_, 0, v___x_2574_);
lean_ctor_set(v___x_2580_, 1, v___x_2576_);
lean_ctor_set(v___x_2580_, 2, v___x_2578_);
lean_ctor_set(v___x_2580_, 3, v___x_2579_);
v___x_2581_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15));
v___x_2582_ = l_Lean_Syntax_node1(v___x_2574_, v___x_2581_, v_a_2565_);
v___x_2583_ = l_Lean_Syntax_node2(v___x_2574_, v___x_2575_, v___x_2580_, v___x_2582_);
if (v_isShared_2569_ == 0)
{
lean_ctor_set(v___x_2568_, 0, v___x_2583_);
v___x_2585_ = v___x_2568_;
goto v_reusejp_2584_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v___x_2583_);
lean_ctor_set(v_reuseFailAlloc_2586_, 1, v_a_2566_);
v___x_2585_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2584_;
}
v_reusejp_2584_:
{
return v___x_2585_;
}
}
}
case 16:
{
uint8_t v_presentation_2588_; lean_object* v___x_2589_; lean_object* v_a_2590_; lean_object* v_a_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2612_; 
v_presentation_2588_ = lean_ctor_get_uint8(v_x_1711_, 0);
lean_dec_ref_known(v_x_1711_, 0);
v___x_2589_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertText(v_presentation_2588_, v_a_1712_, v_a_1713_);
v_a_2590_ = lean_ctor_get(v___x_2589_, 0);
v_a_2591_ = lean_ctor_get(v___x_2589_, 1);
v_isSharedCheck_2612_ = !lean_is_exclusive(v___x_2589_);
if (v_isSharedCheck_2612_ == 0)
{
v___x_2593_ = v___x_2589_;
v_isShared_2594_ = v_isSharedCheck_2612_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_a_2591_);
lean_inc(v_a_2590_);
lean_dec(v___x_2589_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2612_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
lean_object* v_quotContext_2595_; lean_object* v_currMacroScope_2596_; lean_object* v_ref_2597_; uint8_t v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2610_; 
v_quotContext_2595_ = lean_ctor_get(v_a_1712_, 1);
v_currMacroScope_2596_ = lean_ctor_get(v_a_1712_, 2);
v_ref_2597_ = lean_ctor_get(v_a_1712_, 5);
v___x_2598_ = 0;
v___x_2599_ = l_Lean_SourceInfo_fromRef(v_ref_2597_, v___x_2598_);
v___x_2600_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4));
v___x_2601_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__165, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__165_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__165);
v___x_2602_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__167));
lean_inc(v_currMacroScope_2596_);
lean_inc(v_quotContext_2595_);
v___x_2603_ = l_Lean_addMacroScope(v_quotContext_2595_, v___x_2602_, v_currMacroScope_2596_);
v___x_2604_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__171));
lean_inc_n(v___x_2599_, 2);
v___x_2605_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2605_, 0, v___x_2599_);
lean_ctor_set(v___x_2605_, 1, v___x_2601_);
lean_ctor_set(v___x_2605_, 2, v___x_2603_);
lean_ctor_set(v___x_2605_, 3, v___x_2604_);
v___x_2606_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15));
v___x_2607_ = l_Lean_Syntax_node1(v___x_2599_, v___x_2606_, v_a_2590_);
v___x_2608_ = l_Lean_Syntax_node2(v___x_2599_, v___x_2600_, v___x_2605_, v___x_2607_);
if (v_isShared_2594_ == 0)
{
lean_ctor_set(v___x_2593_, 0, v___x_2608_);
v___x_2610_ = v___x_2593_;
goto v_reusejp_2609_;
}
else
{
lean_object* v_reuseFailAlloc_2611_; 
v_reuseFailAlloc_2611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2611_, 0, v___x_2608_);
lean_ctor_set(v_reuseFailAlloc_2611_, 1, v_a_2591_);
v___x_2610_ = v_reuseFailAlloc_2611_;
goto v_reusejp_2609_;
}
v_reusejp_2609_:
{
return v___x_2610_;
}
}
}
case 17:
{
uint8_t v_presentation_2613_; lean_object* v___x_2614_; lean_object* v_a_2615_; lean_object* v_a_2616_; lean_object* v___x_2618_; uint8_t v_isShared_2619_; uint8_t v_isSharedCheck_2637_; 
v_presentation_2613_ = lean_ctor_get_uint8(v_x_1711_, 0);
lean_dec_ref_known(v_x_1711_, 0);
v___x_2614_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertText(v_presentation_2613_, v_a_1712_, v_a_1713_);
v_a_2615_ = lean_ctor_get(v___x_2614_, 0);
v_a_2616_ = lean_ctor_get(v___x_2614_, 1);
v_isSharedCheck_2637_ = !lean_is_exclusive(v___x_2614_);
if (v_isSharedCheck_2637_ == 0)
{
v___x_2618_ = v___x_2614_;
v_isShared_2619_ = v_isSharedCheck_2637_;
goto v_resetjp_2617_;
}
else
{
lean_inc(v_a_2616_);
lean_inc(v_a_2615_);
lean_dec(v___x_2614_);
v___x_2618_ = lean_box(0);
v_isShared_2619_ = v_isSharedCheck_2637_;
goto v_resetjp_2617_;
}
v_resetjp_2617_:
{
lean_object* v_quotContext_2620_; lean_object* v_currMacroScope_2621_; lean_object* v_ref_2622_; uint8_t v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2635_; 
v_quotContext_2620_ = lean_ctor_get(v_a_1712_, 1);
v_currMacroScope_2621_ = lean_ctor_get(v_a_1712_, 2);
v_ref_2622_ = lean_ctor_get(v_a_1712_, 5);
v___x_2623_ = 0;
v___x_2624_ = l_Lean_SourceInfo_fromRef(v_ref_2622_, v___x_2623_);
v___x_2625_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4));
v___x_2626_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__173, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__173_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__173);
v___x_2627_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__175));
lean_inc(v_currMacroScope_2621_);
lean_inc(v_quotContext_2620_);
v___x_2628_ = l_Lean_addMacroScope(v_quotContext_2620_, v___x_2627_, v_currMacroScope_2621_);
v___x_2629_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__179));
lean_inc_n(v___x_2624_, 2);
v___x_2630_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2630_, 0, v___x_2624_);
lean_ctor_set(v___x_2630_, 1, v___x_2626_);
lean_ctor_set(v___x_2630_, 2, v___x_2628_);
lean_ctor_set(v___x_2630_, 3, v___x_2629_);
v___x_2631_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15));
v___x_2632_ = l_Lean_Syntax_node1(v___x_2624_, v___x_2631_, v_a_2615_);
v___x_2633_ = l_Lean_Syntax_node2(v___x_2624_, v___x_2625_, v___x_2630_, v___x_2632_);
if (v_isShared_2619_ == 0)
{
lean_ctor_set(v___x_2618_, 0, v___x_2633_);
v___x_2635_ = v___x_2618_;
goto v_reusejp_2634_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v___x_2633_);
lean_ctor_set(v_reuseFailAlloc_2636_, 1, v_a_2616_);
v___x_2635_ = v_reuseFailAlloc_2636_;
goto v_reusejp_2634_;
}
v_reusejp_2634_:
{
return v___x_2635_;
}
}
}
case 18:
{
uint8_t v_presentation_2638_; lean_object* v___x_2639_; lean_object* v_a_2640_; lean_object* v_a_2641_; lean_object* v___x_2643_; uint8_t v_isShared_2644_; uint8_t v_isSharedCheck_2662_; 
v_presentation_2638_ = lean_ctor_get_uint8(v_x_1711_, 0);
lean_dec_ref_known(v_x_1711_, 0);
v___x_2639_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertText(v_presentation_2638_, v_a_1712_, v_a_1713_);
v_a_2640_ = lean_ctor_get(v___x_2639_, 0);
v_a_2641_ = lean_ctor_get(v___x_2639_, 1);
v_isSharedCheck_2662_ = !lean_is_exclusive(v___x_2639_);
if (v_isSharedCheck_2662_ == 0)
{
v___x_2643_ = v___x_2639_;
v_isShared_2644_ = v_isSharedCheck_2662_;
goto v_resetjp_2642_;
}
else
{
lean_inc(v_a_2641_);
lean_inc(v_a_2640_);
lean_dec(v___x_2639_);
v___x_2643_ = lean_box(0);
v_isShared_2644_ = v_isSharedCheck_2662_;
goto v_resetjp_2642_;
}
v_resetjp_2642_:
{
lean_object* v_quotContext_2645_; lean_object* v_currMacroScope_2646_; lean_object* v_ref_2647_; uint8_t v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2660_; 
v_quotContext_2645_ = lean_ctor_get(v_a_1712_, 1);
v_currMacroScope_2646_ = lean_ctor_get(v_a_1712_, 2);
v_ref_2647_ = lean_ctor_get(v_a_1712_, 5);
v___x_2648_ = 0;
v___x_2649_ = l_Lean_SourceInfo_fromRef(v_ref_2647_, v___x_2648_);
v___x_2650_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4));
v___x_2651_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__181, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__181_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__181);
v___x_2652_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__183));
lean_inc(v_currMacroScope_2646_);
lean_inc(v_quotContext_2645_);
v___x_2653_ = l_Lean_addMacroScope(v_quotContext_2645_, v___x_2652_, v_currMacroScope_2646_);
v___x_2654_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__187));
lean_inc_n(v___x_2649_, 2);
v___x_2655_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2655_, 0, v___x_2649_);
lean_ctor_set(v___x_2655_, 1, v___x_2651_);
lean_ctor_set(v___x_2655_, 2, v___x_2653_);
lean_ctor_set(v___x_2655_, 3, v___x_2654_);
v___x_2656_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15));
v___x_2657_ = l_Lean_Syntax_node1(v___x_2649_, v___x_2656_, v_a_2640_);
v___x_2658_ = l_Lean_Syntax_node2(v___x_2649_, v___x_2650_, v___x_2655_, v___x_2657_);
if (v_isShared_2644_ == 0)
{
lean_ctor_set(v___x_2643_, 0, v___x_2658_);
v___x_2660_ = v___x_2643_;
goto v_reusejp_2659_;
}
else
{
lean_object* v_reuseFailAlloc_2661_; 
v_reuseFailAlloc_2661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2661_, 0, v___x_2658_);
lean_ctor_set(v_reuseFailAlloc_2661_, 1, v_a_2641_);
v___x_2660_ = v_reuseFailAlloc_2661_;
goto v_reusejp_2659_;
}
v_reusejp_2659_:
{
return v___x_2660_;
}
}
}
case 19:
{
lean_object* v_presentation_2663_; lean_object* v___x_2664_; lean_object* v_a_2665_; lean_object* v_a_2666_; lean_object* v___x_2668_; uint8_t v_isShared_2669_; uint8_t v_isSharedCheck_2687_; 
v_presentation_2663_ = lean_ctor_get(v_x_1711_, 0);
lean_inc(v_presentation_2663_);
lean_dec_ref_known(v_x_1711_, 1);
v___x_2664_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber(v_presentation_2663_, v_a_1712_, v_a_1713_);
v_a_2665_ = lean_ctor_get(v___x_2664_, 0);
v_a_2666_ = lean_ctor_get(v___x_2664_, 1);
v_isSharedCheck_2687_ = !lean_is_exclusive(v___x_2664_);
if (v_isSharedCheck_2687_ == 0)
{
v___x_2668_ = v___x_2664_;
v_isShared_2669_ = v_isSharedCheck_2687_;
goto v_resetjp_2667_;
}
else
{
lean_inc(v_a_2666_);
lean_inc(v_a_2665_);
lean_dec(v___x_2664_);
v___x_2668_ = lean_box(0);
v_isShared_2669_ = v_isSharedCheck_2687_;
goto v_resetjp_2667_;
}
v_resetjp_2667_:
{
lean_object* v_quotContext_2670_; lean_object* v_currMacroScope_2671_; lean_object* v_ref_2672_; uint8_t v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2685_; 
v_quotContext_2670_ = lean_ctor_get(v_a_1712_, 1);
v_currMacroScope_2671_ = lean_ctor_get(v_a_1712_, 2);
v_ref_2672_ = lean_ctor_get(v_a_1712_, 5);
v___x_2673_ = 0;
v___x_2674_ = l_Lean_SourceInfo_fromRef(v_ref_2672_, v___x_2673_);
v___x_2675_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4));
v___x_2676_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__189, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__189_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__189);
v___x_2677_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__191));
lean_inc(v_currMacroScope_2671_);
lean_inc(v_quotContext_2670_);
v___x_2678_ = l_Lean_addMacroScope(v_quotContext_2670_, v___x_2677_, v_currMacroScope_2671_);
v___x_2679_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__195));
lean_inc_n(v___x_2674_, 2);
v___x_2680_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2680_, 0, v___x_2674_);
lean_ctor_set(v___x_2680_, 1, v___x_2676_);
lean_ctor_set(v___x_2680_, 2, v___x_2678_);
lean_ctor_set(v___x_2680_, 3, v___x_2679_);
v___x_2681_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15));
v___x_2682_ = l_Lean_Syntax_node1(v___x_2674_, v___x_2681_, v_a_2665_);
v___x_2683_ = l_Lean_Syntax_node2(v___x_2674_, v___x_2675_, v___x_2680_, v___x_2682_);
if (v_isShared_2669_ == 0)
{
lean_ctor_set(v___x_2668_, 0, v___x_2683_);
v___x_2685_ = v___x_2668_;
goto v_reusejp_2684_;
}
else
{
lean_object* v_reuseFailAlloc_2686_; 
v_reuseFailAlloc_2686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2686_, 0, v___x_2683_);
lean_ctor_set(v_reuseFailAlloc_2686_, 1, v_a_2666_);
v___x_2685_ = v_reuseFailAlloc_2686_;
goto v_reusejp_2684_;
}
v_reusejp_2684_:
{
return v___x_2685_;
}
}
}
case 20:
{
lean_object* v_presentation_2688_; lean_object* v___x_2689_; lean_object* v_a_2690_; lean_object* v_a_2691_; lean_object* v___x_2693_; uint8_t v_isShared_2694_; uint8_t v_isSharedCheck_2712_; 
v_presentation_2688_ = lean_ctor_get(v_x_1711_, 0);
lean_inc(v_presentation_2688_);
lean_dec_ref_known(v_x_1711_, 1);
v___x_2689_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber(v_presentation_2688_, v_a_1712_, v_a_1713_);
v_a_2690_ = lean_ctor_get(v___x_2689_, 0);
v_a_2691_ = lean_ctor_get(v___x_2689_, 1);
v_isSharedCheck_2712_ = !lean_is_exclusive(v___x_2689_);
if (v_isSharedCheck_2712_ == 0)
{
v___x_2693_ = v___x_2689_;
v_isShared_2694_ = v_isSharedCheck_2712_;
goto v_resetjp_2692_;
}
else
{
lean_inc(v_a_2691_);
lean_inc(v_a_2690_);
lean_dec(v___x_2689_);
v___x_2693_ = lean_box(0);
v_isShared_2694_ = v_isSharedCheck_2712_;
goto v_resetjp_2692_;
}
v_resetjp_2692_:
{
lean_object* v_quotContext_2695_; lean_object* v_currMacroScope_2696_; lean_object* v_ref_2697_; uint8_t v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2710_; 
v_quotContext_2695_ = lean_ctor_get(v_a_1712_, 1);
v_currMacroScope_2696_ = lean_ctor_get(v_a_1712_, 2);
v_ref_2697_ = lean_ctor_get(v_a_1712_, 5);
v___x_2698_ = 0;
v___x_2699_ = l_Lean_SourceInfo_fromRef(v_ref_2697_, v___x_2698_);
v___x_2700_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4));
v___x_2701_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__197, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__197_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__197);
v___x_2702_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__199));
lean_inc(v_currMacroScope_2696_);
lean_inc(v_quotContext_2695_);
v___x_2703_ = l_Lean_addMacroScope(v_quotContext_2695_, v___x_2702_, v_currMacroScope_2696_);
v___x_2704_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__203));
lean_inc_n(v___x_2699_, 2);
v___x_2705_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2705_, 0, v___x_2699_);
lean_ctor_set(v___x_2705_, 1, v___x_2701_);
lean_ctor_set(v___x_2705_, 2, v___x_2703_);
lean_ctor_set(v___x_2705_, 3, v___x_2704_);
v___x_2706_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15));
v___x_2707_ = l_Lean_Syntax_node1(v___x_2699_, v___x_2706_, v_a_2690_);
v___x_2708_ = l_Lean_Syntax_node2(v___x_2699_, v___x_2700_, v___x_2705_, v___x_2707_);
if (v_isShared_2694_ == 0)
{
lean_ctor_set(v___x_2693_, 0, v___x_2708_);
v___x_2710_ = v___x_2693_;
goto v_reusejp_2709_;
}
else
{
lean_object* v_reuseFailAlloc_2711_; 
v_reuseFailAlloc_2711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2711_, 0, v___x_2708_);
lean_ctor_set(v_reuseFailAlloc_2711_, 1, v_a_2691_);
v___x_2710_ = v_reuseFailAlloc_2711_;
goto v_reusejp_2709_;
}
v_reusejp_2709_:
{
return v___x_2710_;
}
}
}
case 21:
{
lean_object* v_presentation_2713_; lean_object* v___x_2714_; lean_object* v_a_2715_; lean_object* v_a_2716_; lean_object* v___x_2718_; uint8_t v_isShared_2719_; uint8_t v_isSharedCheck_2737_; 
v_presentation_2713_ = lean_ctor_get(v_x_1711_, 0);
lean_inc(v_presentation_2713_);
lean_dec_ref_known(v_x_1711_, 1);
v___x_2714_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber(v_presentation_2713_, v_a_1712_, v_a_1713_);
v_a_2715_ = lean_ctor_get(v___x_2714_, 0);
v_a_2716_ = lean_ctor_get(v___x_2714_, 1);
v_isSharedCheck_2737_ = !lean_is_exclusive(v___x_2714_);
if (v_isSharedCheck_2737_ == 0)
{
v___x_2718_ = v___x_2714_;
v_isShared_2719_ = v_isSharedCheck_2737_;
goto v_resetjp_2717_;
}
else
{
lean_inc(v_a_2716_);
lean_inc(v_a_2715_);
lean_dec(v___x_2714_);
v___x_2718_ = lean_box(0);
v_isShared_2719_ = v_isSharedCheck_2737_;
goto v_resetjp_2717_;
}
v_resetjp_2717_:
{
lean_object* v_quotContext_2720_; lean_object* v_currMacroScope_2721_; lean_object* v_ref_2722_; uint8_t v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2735_; 
v_quotContext_2720_ = lean_ctor_get(v_a_1712_, 1);
v_currMacroScope_2721_ = lean_ctor_get(v_a_1712_, 2);
v_ref_2722_ = lean_ctor_get(v_a_1712_, 5);
v___x_2723_ = 0;
v___x_2724_ = l_Lean_SourceInfo_fromRef(v_ref_2722_, v___x_2723_);
v___x_2725_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4));
v___x_2726_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__205, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__205_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__205);
v___x_2727_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__207));
lean_inc(v_currMacroScope_2721_);
lean_inc(v_quotContext_2720_);
v___x_2728_ = l_Lean_addMacroScope(v_quotContext_2720_, v___x_2727_, v_currMacroScope_2721_);
v___x_2729_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__211));
lean_inc_n(v___x_2724_, 2);
v___x_2730_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2730_, 0, v___x_2724_);
lean_ctor_set(v___x_2730_, 1, v___x_2726_);
lean_ctor_set(v___x_2730_, 2, v___x_2728_);
lean_ctor_set(v___x_2730_, 3, v___x_2729_);
v___x_2731_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15));
v___x_2732_ = l_Lean_Syntax_node1(v___x_2724_, v___x_2731_, v_a_2715_);
v___x_2733_ = l_Lean_Syntax_node2(v___x_2724_, v___x_2725_, v___x_2730_, v___x_2732_);
if (v_isShared_2719_ == 0)
{
lean_ctor_set(v___x_2718_, 0, v___x_2733_);
v___x_2735_ = v___x_2718_;
goto v_reusejp_2734_;
}
else
{
lean_object* v_reuseFailAlloc_2736_; 
v_reuseFailAlloc_2736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2736_, 0, v___x_2733_);
lean_ctor_set(v_reuseFailAlloc_2736_, 1, v_a_2716_);
v___x_2735_ = v_reuseFailAlloc_2736_;
goto v_reusejp_2734_;
}
v_reusejp_2734_:
{
return v___x_2735_;
}
}
}
case 22:
{
lean_object* v_presentation_2738_; lean_object* v___x_2739_; lean_object* v_a_2740_; lean_object* v_a_2741_; lean_object* v___x_2743_; uint8_t v_isShared_2744_; uint8_t v_isSharedCheck_2762_; 
v_presentation_2738_ = lean_ctor_get(v_x_1711_, 0);
lean_inc(v_presentation_2738_);
lean_dec_ref_known(v_x_1711_, 1);
v___x_2739_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber(v_presentation_2738_, v_a_1712_, v_a_1713_);
v_a_2740_ = lean_ctor_get(v___x_2739_, 0);
v_a_2741_ = lean_ctor_get(v___x_2739_, 1);
v_isSharedCheck_2762_ = !lean_is_exclusive(v___x_2739_);
if (v_isSharedCheck_2762_ == 0)
{
v___x_2743_ = v___x_2739_;
v_isShared_2744_ = v_isSharedCheck_2762_;
goto v_resetjp_2742_;
}
else
{
lean_inc(v_a_2741_);
lean_inc(v_a_2740_);
lean_dec(v___x_2739_);
v___x_2743_ = lean_box(0);
v_isShared_2744_ = v_isSharedCheck_2762_;
goto v_resetjp_2742_;
}
v_resetjp_2742_:
{
lean_object* v_quotContext_2745_; lean_object* v_currMacroScope_2746_; lean_object* v_ref_2747_; uint8_t v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2760_; 
v_quotContext_2745_ = lean_ctor_get(v_a_1712_, 1);
v_currMacroScope_2746_ = lean_ctor_get(v_a_1712_, 2);
v_ref_2747_ = lean_ctor_get(v_a_1712_, 5);
v___x_2748_ = 0;
v___x_2749_ = l_Lean_SourceInfo_fromRef(v_ref_2747_, v___x_2748_);
v___x_2750_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4));
v___x_2751_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__213, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__213_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__213);
v___x_2752_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__215));
lean_inc(v_currMacroScope_2746_);
lean_inc(v_quotContext_2745_);
v___x_2753_ = l_Lean_addMacroScope(v_quotContext_2745_, v___x_2752_, v_currMacroScope_2746_);
v___x_2754_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__219));
lean_inc_n(v___x_2749_, 2);
v___x_2755_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2755_, 0, v___x_2749_);
lean_ctor_set(v___x_2755_, 1, v___x_2751_);
lean_ctor_set(v___x_2755_, 2, v___x_2753_);
lean_ctor_set(v___x_2755_, 3, v___x_2754_);
v___x_2756_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15));
v___x_2757_ = l_Lean_Syntax_node1(v___x_2749_, v___x_2756_, v_a_2740_);
v___x_2758_ = l_Lean_Syntax_node2(v___x_2749_, v___x_2750_, v___x_2755_, v___x_2757_);
if (v_isShared_2744_ == 0)
{
lean_ctor_set(v___x_2743_, 0, v___x_2758_);
v___x_2760_ = v___x_2743_;
goto v_reusejp_2759_;
}
else
{
lean_object* v_reuseFailAlloc_2761_; 
v_reuseFailAlloc_2761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2761_, 0, v___x_2758_);
lean_ctor_set(v_reuseFailAlloc_2761_, 1, v_a_2741_);
v___x_2760_ = v_reuseFailAlloc_2761_;
goto v_reusejp_2759_;
}
v_reusejp_2759_:
{
return v___x_2760_;
}
}
}
case 23:
{
lean_object* v_presentation_2763_; lean_object* v___x_2764_; lean_object* v_a_2765_; lean_object* v_a_2766_; lean_object* v___x_2768_; uint8_t v_isShared_2769_; uint8_t v_isSharedCheck_2787_; 
v_presentation_2763_ = lean_ctor_get(v_x_1711_, 0);
lean_inc(v_presentation_2763_);
lean_dec_ref_known(v_x_1711_, 1);
v___x_2764_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber(v_presentation_2763_, v_a_1712_, v_a_1713_);
v_a_2765_ = lean_ctor_get(v___x_2764_, 0);
v_a_2766_ = lean_ctor_get(v___x_2764_, 1);
v_isSharedCheck_2787_ = !lean_is_exclusive(v___x_2764_);
if (v_isSharedCheck_2787_ == 0)
{
v___x_2768_ = v___x_2764_;
v_isShared_2769_ = v_isSharedCheck_2787_;
goto v_resetjp_2767_;
}
else
{
lean_inc(v_a_2766_);
lean_inc(v_a_2765_);
lean_dec(v___x_2764_);
v___x_2768_ = lean_box(0);
v_isShared_2769_ = v_isSharedCheck_2787_;
goto v_resetjp_2767_;
}
v_resetjp_2767_:
{
lean_object* v_quotContext_2770_; lean_object* v_currMacroScope_2771_; lean_object* v_ref_2772_; uint8_t v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2785_; 
v_quotContext_2770_ = lean_ctor_get(v_a_1712_, 1);
v_currMacroScope_2771_ = lean_ctor_get(v_a_1712_, 2);
v_ref_2772_ = lean_ctor_get(v_a_1712_, 5);
v___x_2773_ = 0;
v___x_2774_ = l_Lean_SourceInfo_fromRef(v_ref_2772_, v___x_2773_);
v___x_2775_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4));
v___x_2776_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__221, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__221_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__221);
v___x_2777_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__223));
lean_inc(v_currMacroScope_2771_);
lean_inc(v_quotContext_2770_);
v___x_2778_ = l_Lean_addMacroScope(v_quotContext_2770_, v___x_2777_, v_currMacroScope_2771_);
v___x_2779_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__227));
lean_inc_n(v___x_2774_, 2);
v___x_2780_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2780_, 0, v___x_2774_);
lean_ctor_set(v___x_2780_, 1, v___x_2776_);
lean_ctor_set(v___x_2780_, 2, v___x_2778_);
lean_ctor_set(v___x_2780_, 3, v___x_2779_);
v___x_2781_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15));
v___x_2782_ = l_Lean_Syntax_node1(v___x_2774_, v___x_2781_, v_a_2765_);
v___x_2783_ = l_Lean_Syntax_node2(v___x_2774_, v___x_2775_, v___x_2780_, v___x_2782_);
if (v_isShared_2769_ == 0)
{
lean_ctor_set(v___x_2768_, 0, v___x_2783_);
v___x_2785_ = v___x_2768_;
goto v_reusejp_2784_;
}
else
{
lean_object* v_reuseFailAlloc_2786_; 
v_reuseFailAlloc_2786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2786_, 0, v___x_2783_);
lean_ctor_set(v_reuseFailAlloc_2786_, 1, v_a_2766_);
v___x_2785_ = v_reuseFailAlloc_2786_;
goto v_reusejp_2784_;
}
v_reusejp_2784_:
{
return v___x_2785_;
}
}
}
case 24:
{
lean_object* v_presentation_2788_; lean_object* v___x_2789_; lean_object* v_a_2790_; lean_object* v_a_2791_; lean_object* v___x_2793_; uint8_t v_isShared_2794_; uint8_t v_isSharedCheck_2812_; 
v_presentation_2788_ = lean_ctor_get(v_x_1711_, 0);
lean_inc(v_presentation_2788_);
lean_dec_ref_known(v_x_1711_, 1);
v___x_2789_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber(v_presentation_2788_, v_a_1712_, v_a_1713_);
v_a_2790_ = lean_ctor_get(v___x_2789_, 0);
v_a_2791_ = lean_ctor_get(v___x_2789_, 1);
v_isSharedCheck_2812_ = !lean_is_exclusive(v___x_2789_);
if (v_isSharedCheck_2812_ == 0)
{
v___x_2793_ = v___x_2789_;
v_isShared_2794_ = v_isSharedCheck_2812_;
goto v_resetjp_2792_;
}
else
{
lean_inc(v_a_2791_);
lean_inc(v_a_2790_);
lean_dec(v___x_2789_);
v___x_2793_ = lean_box(0);
v_isShared_2794_ = v_isSharedCheck_2812_;
goto v_resetjp_2792_;
}
v_resetjp_2792_:
{
lean_object* v_quotContext_2795_; lean_object* v_currMacroScope_2796_; lean_object* v_ref_2797_; uint8_t v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2810_; 
v_quotContext_2795_ = lean_ctor_get(v_a_1712_, 1);
v_currMacroScope_2796_ = lean_ctor_get(v_a_1712_, 2);
v_ref_2797_ = lean_ctor_get(v_a_1712_, 5);
v___x_2798_ = 0;
v___x_2799_ = l_Lean_SourceInfo_fromRef(v_ref_2797_, v___x_2798_);
v___x_2800_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4));
v___x_2801_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__229, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__229_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__229);
v___x_2802_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__231));
lean_inc(v_currMacroScope_2796_);
lean_inc(v_quotContext_2795_);
v___x_2803_ = l_Lean_addMacroScope(v_quotContext_2795_, v___x_2802_, v_currMacroScope_2796_);
v___x_2804_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__235));
lean_inc_n(v___x_2799_, 2);
v___x_2805_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2805_, 0, v___x_2799_);
lean_ctor_set(v___x_2805_, 1, v___x_2801_);
lean_ctor_set(v___x_2805_, 2, v___x_2803_);
lean_ctor_set(v___x_2805_, 3, v___x_2804_);
v___x_2806_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15));
v___x_2807_ = l_Lean_Syntax_node1(v___x_2799_, v___x_2806_, v_a_2790_);
v___x_2808_ = l_Lean_Syntax_node2(v___x_2799_, v___x_2800_, v___x_2805_, v___x_2807_);
if (v_isShared_2794_ == 0)
{
lean_ctor_set(v___x_2793_, 0, v___x_2808_);
v___x_2810_ = v___x_2793_;
goto v_reusejp_2809_;
}
else
{
lean_object* v_reuseFailAlloc_2811_; 
v_reuseFailAlloc_2811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2811_, 0, v___x_2808_);
lean_ctor_set(v_reuseFailAlloc_2811_, 1, v_a_2791_);
v___x_2810_ = v_reuseFailAlloc_2811_;
goto v_reusejp_2809_;
}
v_reusejp_2809_:
{
return v___x_2810_;
}
}
}
case 25:
{
lean_object* v_presentation_2813_; lean_object* v___x_2814_; lean_object* v_a_2815_; lean_object* v_a_2816_; lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_2837_; 
v_presentation_2813_ = lean_ctor_get(v_x_1711_, 0);
lean_inc(v_presentation_2813_);
lean_dec_ref_known(v_x_1711_, 1);
v___x_2814_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction(v_presentation_2813_, v_a_1712_, v_a_1713_);
v_a_2815_ = lean_ctor_get(v___x_2814_, 0);
v_a_2816_ = lean_ctor_get(v___x_2814_, 1);
v_isSharedCheck_2837_ = !lean_is_exclusive(v___x_2814_);
if (v_isSharedCheck_2837_ == 0)
{
v___x_2818_ = v___x_2814_;
v_isShared_2819_ = v_isSharedCheck_2837_;
goto v_resetjp_2817_;
}
else
{
lean_inc(v_a_2816_);
lean_inc(v_a_2815_);
lean_dec(v___x_2814_);
v___x_2818_ = lean_box(0);
v_isShared_2819_ = v_isSharedCheck_2837_;
goto v_resetjp_2817_;
}
v_resetjp_2817_:
{
lean_object* v_quotContext_2820_; lean_object* v_currMacroScope_2821_; lean_object* v_ref_2822_; uint8_t v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2835_; 
v_quotContext_2820_ = lean_ctor_get(v_a_1712_, 1);
v_currMacroScope_2821_ = lean_ctor_get(v_a_1712_, 2);
v_ref_2822_ = lean_ctor_get(v_a_1712_, 5);
v___x_2823_ = 0;
v___x_2824_ = l_Lean_SourceInfo_fromRef(v_ref_2822_, v___x_2823_);
v___x_2825_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4));
v___x_2826_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__237, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__237_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__237);
v___x_2827_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__239));
lean_inc(v_currMacroScope_2821_);
lean_inc(v_quotContext_2820_);
v___x_2828_ = l_Lean_addMacroScope(v_quotContext_2820_, v___x_2827_, v_currMacroScope_2821_);
v___x_2829_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__243));
lean_inc_n(v___x_2824_, 2);
v___x_2830_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2830_, 0, v___x_2824_);
lean_ctor_set(v___x_2830_, 1, v___x_2826_);
lean_ctor_set(v___x_2830_, 2, v___x_2828_);
lean_ctor_set(v___x_2830_, 3, v___x_2829_);
v___x_2831_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15));
v___x_2832_ = l_Lean_Syntax_node1(v___x_2824_, v___x_2831_, v_a_2815_);
v___x_2833_ = l_Lean_Syntax_node2(v___x_2824_, v___x_2825_, v___x_2830_, v___x_2832_);
if (v_isShared_2819_ == 0)
{
lean_ctor_set(v___x_2818_, 0, v___x_2833_);
v___x_2835_ = v___x_2818_;
goto v_reusejp_2834_;
}
else
{
lean_object* v_reuseFailAlloc_2836_; 
v_reuseFailAlloc_2836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2836_, 0, v___x_2833_);
lean_ctor_set(v_reuseFailAlloc_2836_, 1, v_a_2816_);
v___x_2835_ = v_reuseFailAlloc_2836_;
goto v_reusejp_2834_;
}
v_reusejp_2834_:
{
return v___x_2835_;
}
}
}
case 26:
{
lean_object* v_presentation_2838_; lean_object* v___x_2839_; lean_object* v_a_2840_; lean_object* v_a_2841_; lean_object* v___x_2843_; uint8_t v_isShared_2844_; uint8_t v_isSharedCheck_2862_; 
v_presentation_2838_ = lean_ctor_get(v_x_1711_, 0);
lean_inc(v_presentation_2838_);
lean_dec_ref_known(v_x_1711_, 1);
v___x_2839_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber(v_presentation_2838_, v_a_1712_, v_a_1713_);
v_a_2840_ = lean_ctor_get(v___x_2839_, 0);
v_a_2841_ = lean_ctor_get(v___x_2839_, 1);
v_isSharedCheck_2862_ = !lean_is_exclusive(v___x_2839_);
if (v_isSharedCheck_2862_ == 0)
{
v___x_2843_ = v___x_2839_;
v_isShared_2844_ = v_isSharedCheck_2862_;
goto v_resetjp_2842_;
}
else
{
lean_inc(v_a_2841_);
lean_inc(v_a_2840_);
lean_dec(v___x_2839_);
v___x_2843_ = lean_box(0);
v_isShared_2844_ = v_isSharedCheck_2862_;
goto v_resetjp_2842_;
}
v_resetjp_2842_:
{
lean_object* v_quotContext_2845_; lean_object* v_currMacroScope_2846_; lean_object* v_ref_2847_; uint8_t v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2860_; 
v_quotContext_2845_ = lean_ctor_get(v_a_1712_, 1);
v_currMacroScope_2846_ = lean_ctor_get(v_a_1712_, 2);
v_ref_2847_ = lean_ctor_get(v_a_1712_, 5);
v___x_2848_ = 0;
v___x_2849_ = l_Lean_SourceInfo_fromRef(v_ref_2847_, v___x_2848_);
v___x_2850_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4));
v___x_2851_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__245, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__245_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__245);
v___x_2852_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__247));
lean_inc(v_currMacroScope_2846_);
lean_inc(v_quotContext_2845_);
v___x_2853_ = l_Lean_addMacroScope(v_quotContext_2845_, v___x_2852_, v_currMacroScope_2846_);
v___x_2854_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__251));
lean_inc_n(v___x_2849_, 2);
v___x_2855_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2855_, 0, v___x_2849_);
lean_ctor_set(v___x_2855_, 1, v___x_2851_);
lean_ctor_set(v___x_2855_, 2, v___x_2853_);
lean_ctor_set(v___x_2855_, 3, v___x_2854_);
v___x_2856_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15));
v___x_2857_ = l_Lean_Syntax_node1(v___x_2849_, v___x_2856_, v_a_2840_);
v___x_2858_ = l_Lean_Syntax_node2(v___x_2849_, v___x_2850_, v___x_2855_, v___x_2857_);
if (v_isShared_2844_ == 0)
{
lean_ctor_set(v___x_2843_, 0, v___x_2858_);
v___x_2860_ = v___x_2843_;
goto v_reusejp_2859_;
}
else
{
lean_object* v_reuseFailAlloc_2861_; 
v_reuseFailAlloc_2861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2861_, 0, v___x_2858_);
lean_ctor_set(v_reuseFailAlloc_2861_, 1, v_a_2841_);
v___x_2860_ = v_reuseFailAlloc_2861_;
goto v_reusejp_2859_;
}
v_reusejp_2859_:
{
return v___x_2860_;
}
}
}
case 27:
{
lean_object* v_presentation_2863_; lean_object* v___x_2864_; lean_object* v_a_2865_; lean_object* v_a_2866_; lean_object* v___x_2868_; uint8_t v_isShared_2869_; uint8_t v_isSharedCheck_2887_; 
v_presentation_2863_ = lean_ctor_get(v_x_1711_, 0);
lean_inc(v_presentation_2863_);
lean_dec_ref_known(v_x_1711_, 1);
v___x_2864_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber(v_presentation_2863_, v_a_1712_, v_a_1713_);
v_a_2865_ = lean_ctor_get(v___x_2864_, 0);
v_a_2866_ = lean_ctor_get(v___x_2864_, 1);
v_isSharedCheck_2887_ = !lean_is_exclusive(v___x_2864_);
if (v_isSharedCheck_2887_ == 0)
{
v___x_2868_ = v___x_2864_;
v_isShared_2869_ = v_isSharedCheck_2887_;
goto v_resetjp_2867_;
}
else
{
lean_inc(v_a_2866_);
lean_inc(v_a_2865_);
lean_dec(v___x_2864_);
v___x_2868_ = lean_box(0);
v_isShared_2869_ = v_isSharedCheck_2887_;
goto v_resetjp_2867_;
}
v_resetjp_2867_:
{
lean_object* v_quotContext_2870_; lean_object* v_currMacroScope_2871_; lean_object* v_ref_2872_; uint8_t v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2885_; 
v_quotContext_2870_ = lean_ctor_get(v_a_1712_, 1);
v_currMacroScope_2871_ = lean_ctor_get(v_a_1712_, 2);
v_ref_2872_ = lean_ctor_get(v_a_1712_, 5);
v___x_2873_ = 0;
v___x_2874_ = l_Lean_SourceInfo_fromRef(v_ref_2872_, v___x_2873_);
v___x_2875_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4));
v___x_2876_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__253, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__253_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__253);
v___x_2877_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__255));
lean_inc(v_currMacroScope_2871_);
lean_inc(v_quotContext_2870_);
v___x_2878_ = l_Lean_addMacroScope(v_quotContext_2870_, v___x_2877_, v_currMacroScope_2871_);
v___x_2879_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__259));
lean_inc_n(v___x_2874_, 2);
v___x_2880_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2880_, 0, v___x_2874_);
lean_ctor_set(v___x_2880_, 1, v___x_2876_);
lean_ctor_set(v___x_2880_, 2, v___x_2878_);
lean_ctor_set(v___x_2880_, 3, v___x_2879_);
v___x_2881_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15));
v___x_2882_ = l_Lean_Syntax_node1(v___x_2874_, v___x_2881_, v_a_2865_);
v___x_2883_ = l_Lean_Syntax_node2(v___x_2874_, v___x_2875_, v___x_2880_, v___x_2882_);
if (v_isShared_2869_ == 0)
{
lean_ctor_set(v___x_2868_, 0, v___x_2883_);
v___x_2885_ = v___x_2868_;
goto v_reusejp_2884_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v___x_2883_);
lean_ctor_set(v_reuseFailAlloc_2886_, 1, v_a_2866_);
v___x_2885_ = v_reuseFailAlloc_2886_;
goto v_reusejp_2884_;
}
v_reusejp_2884_:
{
return v___x_2885_;
}
}
}
case 28:
{
lean_object* v_presentation_2888_; lean_object* v___x_2889_; lean_object* v_a_2890_; lean_object* v_a_2891_; lean_object* v___x_2893_; uint8_t v_isShared_2894_; uint8_t v_isSharedCheck_2912_; 
v_presentation_2888_ = lean_ctor_get(v_x_1711_, 0);
lean_inc(v_presentation_2888_);
lean_dec_ref_known(v_x_1711_, 1);
v___x_2889_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber(v_presentation_2888_, v_a_1712_, v_a_1713_);
v_a_2890_ = lean_ctor_get(v___x_2889_, 0);
v_a_2891_ = lean_ctor_get(v___x_2889_, 1);
v_isSharedCheck_2912_ = !lean_is_exclusive(v___x_2889_);
if (v_isSharedCheck_2912_ == 0)
{
v___x_2893_ = v___x_2889_;
v_isShared_2894_ = v_isSharedCheck_2912_;
goto v_resetjp_2892_;
}
else
{
lean_inc(v_a_2891_);
lean_inc(v_a_2890_);
lean_dec(v___x_2889_);
v___x_2893_ = lean_box(0);
v_isShared_2894_ = v_isSharedCheck_2912_;
goto v_resetjp_2892_;
}
v_resetjp_2892_:
{
lean_object* v_quotContext_2895_; lean_object* v_currMacroScope_2896_; lean_object* v_ref_2897_; uint8_t v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2910_; 
v_quotContext_2895_ = lean_ctor_get(v_a_1712_, 1);
v_currMacroScope_2896_ = lean_ctor_get(v_a_1712_, 2);
v_ref_2897_ = lean_ctor_get(v_a_1712_, 5);
v___x_2898_ = 0;
v___x_2899_ = l_Lean_SourceInfo_fromRef(v_ref_2897_, v___x_2898_);
v___x_2900_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4));
v___x_2901_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__261, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__261_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__261);
v___x_2902_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__263));
lean_inc(v_currMacroScope_2896_);
lean_inc(v_quotContext_2895_);
v___x_2903_ = l_Lean_addMacroScope(v_quotContext_2895_, v___x_2902_, v_currMacroScope_2896_);
v___x_2904_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__267));
lean_inc_n(v___x_2899_, 2);
v___x_2905_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2905_, 0, v___x_2899_);
lean_ctor_set(v___x_2905_, 1, v___x_2901_);
lean_ctor_set(v___x_2905_, 2, v___x_2903_);
lean_ctor_set(v___x_2905_, 3, v___x_2904_);
v___x_2906_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15));
v___x_2907_ = l_Lean_Syntax_node1(v___x_2899_, v___x_2906_, v_a_2890_);
v___x_2908_ = l_Lean_Syntax_node2(v___x_2899_, v___x_2900_, v___x_2905_, v___x_2907_);
if (v_isShared_2894_ == 0)
{
lean_ctor_set(v___x_2893_, 0, v___x_2908_);
v___x_2910_ = v___x_2893_;
goto v_reusejp_2909_;
}
else
{
lean_object* v_reuseFailAlloc_2911_; 
v_reuseFailAlloc_2911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2911_, 0, v___x_2908_);
lean_ctor_set(v_reuseFailAlloc_2911_, 1, v_a_2891_);
v___x_2910_ = v_reuseFailAlloc_2911_;
goto v_reusejp_2909_;
}
v_reusejp_2909_:
{
return v___x_2910_;
}
}
}
case 29:
{
uint8_t v_presentation_2913_; lean_object* v___x_2914_; lean_object* v_a_2915_; lean_object* v_a_2916_; lean_object* v___x_2918_; uint8_t v_isShared_2919_; uint8_t v_isSharedCheck_2937_; 
v_presentation_2913_ = lean_ctor_get_uint8(v_x_1711_, 0);
lean_dec_ref_known(v_x_1711_, 0);
v___x_2914_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneId(v_presentation_2913_, v_a_1712_, v_a_1713_);
v_a_2915_ = lean_ctor_get(v___x_2914_, 0);
v_a_2916_ = lean_ctor_get(v___x_2914_, 1);
v_isSharedCheck_2937_ = !lean_is_exclusive(v___x_2914_);
if (v_isSharedCheck_2937_ == 0)
{
v___x_2918_ = v___x_2914_;
v_isShared_2919_ = v_isSharedCheck_2937_;
goto v_resetjp_2917_;
}
else
{
lean_inc(v_a_2916_);
lean_inc(v_a_2915_);
lean_dec(v___x_2914_);
v___x_2918_ = lean_box(0);
v_isShared_2919_ = v_isSharedCheck_2937_;
goto v_resetjp_2917_;
}
v_resetjp_2917_:
{
lean_object* v_quotContext_2920_; lean_object* v_currMacroScope_2921_; lean_object* v_ref_2922_; uint8_t v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2935_; 
v_quotContext_2920_ = lean_ctor_get(v_a_1712_, 1);
v_currMacroScope_2921_ = lean_ctor_get(v_a_1712_, 2);
v_ref_2922_ = lean_ctor_get(v_a_1712_, 5);
v___x_2923_ = 0;
v___x_2924_ = l_Lean_SourceInfo_fromRef(v_ref_2922_, v___x_2923_);
v___x_2925_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4));
v___x_2926_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__269, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__269_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__269);
v___x_2927_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__271));
lean_inc(v_currMacroScope_2921_);
lean_inc(v_quotContext_2920_);
v___x_2928_ = l_Lean_addMacroScope(v_quotContext_2920_, v___x_2927_, v_currMacroScope_2921_);
v___x_2929_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__275));
lean_inc_n(v___x_2924_, 2);
v___x_2930_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2930_, 0, v___x_2924_);
lean_ctor_set(v___x_2930_, 1, v___x_2926_);
lean_ctor_set(v___x_2930_, 2, v___x_2928_);
lean_ctor_set(v___x_2930_, 3, v___x_2929_);
v___x_2931_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15));
v___x_2932_ = l_Lean_Syntax_node1(v___x_2924_, v___x_2931_, v_a_2915_);
v___x_2933_ = l_Lean_Syntax_node2(v___x_2924_, v___x_2925_, v___x_2930_, v___x_2932_);
if (v_isShared_2919_ == 0)
{
lean_ctor_set(v___x_2918_, 0, v___x_2933_);
v___x_2935_ = v___x_2918_;
goto v_reusejp_2934_;
}
else
{
lean_object* v_reuseFailAlloc_2936_; 
v_reuseFailAlloc_2936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2936_, 0, v___x_2933_);
lean_ctor_set(v_reuseFailAlloc_2936_, 1, v_a_2916_);
v___x_2935_ = v_reuseFailAlloc_2936_;
goto v_reusejp_2934_;
}
v_reusejp_2934_:
{
return v___x_2935_;
}
}
}
case 30:
{
uint8_t v_presentation_2938_; lean_object* v___x_2939_; lean_object* v_a_2940_; lean_object* v_a_2941_; lean_object* v___x_2943_; uint8_t v_isShared_2944_; uint8_t v_isSharedCheck_2962_; 
v_presentation_2938_ = lean_ctor_get_uint8(v_x_1711_, 0);
lean_dec_ref_known(v_x_1711_, 0);
v___x_2939_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName(v_presentation_2938_, v_a_1712_, v_a_1713_);
v_a_2940_ = lean_ctor_get(v___x_2939_, 0);
v_a_2941_ = lean_ctor_get(v___x_2939_, 1);
v_isSharedCheck_2962_ = !lean_is_exclusive(v___x_2939_);
if (v_isSharedCheck_2962_ == 0)
{
v___x_2943_ = v___x_2939_;
v_isShared_2944_ = v_isSharedCheck_2962_;
goto v_resetjp_2942_;
}
else
{
lean_inc(v_a_2941_);
lean_inc(v_a_2940_);
lean_dec(v___x_2939_);
v___x_2943_ = lean_box(0);
v_isShared_2944_ = v_isSharedCheck_2962_;
goto v_resetjp_2942_;
}
v_resetjp_2942_:
{
lean_object* v_quotContext_2945_; lean_object* v_currMacroScope_2946_; lean_object* v_ref_2947_; uint8_t v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2960_; 
v_quotContext_2945_ = lean_ctor_get(v_a_1712_, 1);
v_currMacroScope_2946_ = lean_ctor_get(v_a_1712_, 2);
v_ref_2947_ = lean_ctor_get(v_a_1712_, 5);
v___x_2948_ = 0;
v___x_2949_ = l_Lean_SourceInfo_fromRef(v_ref_2947_, v___x_2948_);
v___x_2950_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4));
v___x_2951_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__277, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__277_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__277);
v___x_2952_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__279));
lean_inc(v_currMacroScope_2946_);
lean_inc(v_quotContext_2945_);
v___x_2953_ = l_Lean_addMacroScope(v_quotContext_2945_, v___x_2952_, v_currMacroScope_2946_);
v___x_2954_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__283));
lean_inc_n(v___x_2949_, 2);
v___x_2955_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2955_, 0, v___x_2949_);
lean_ctor_set(v___x_2955_, 1, v___x_2951_);
lean_ctor_set(v___x_2955_, 2, v___x_2953_);
lean_ctor_set(v___x_2955_, 3, v___x_2954_);
v___x_2956_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15));
v___x_2957_ = l_Lean_Syntax_node1(v___x_2949_, v___x_2956_, v_a_2940_);
v___x_2958_ = l_Lean_Syntax_node2(v___x_2949_, v___x_2950_, v___x_2955_, v___x_2957_);
if (v_isShared_2944_ == 0)
{
lean_ctor_set(v___x_2943_, 0, v___x_2958_);
v___x_2960_ = v___x_2943_;
goto v_reusejp_2959_;
}
else
{
lean_object* v_reuseFailAlloc_2961_; 
v_reuseFailAlloc_2961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2961_, 0, v___x_2958_);
lean_ctor_set(v_reuseFailAlloc_2961_, 1, v_a_2941_);
v___x_2960_ = v_reuseFailAlloc_2961_;
goto v_reusejp_2959_;
}
v_reusejp_2959_:
{
return v___x_2960_;
}
}
}
case 31:
{
uint8_t v_presentation_2963_; lean_object* v___x_2964_; lean_object* v_a_2965_; lean_object* v_a_2966_; lean_object* v___x_2968_; uint8_t v_isShared_2969_; uint8_t v_isSharedCheck_2987_; 
v_presentation_2963_ = lean_ctor_get_uint8(v_x_1711_, 0);
lean_dec_ref_known(v_x_1711_, 0);
v___x_2964_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName(v_presentation_2963_, v_a_1712_, v_a_1713_);
v_a_2965_ = lean_ctor_get(v___x_2964_, 0);
v_a_2966_ = lean_ctor_get(v___x_2964_, 1);
v_isSharedCheck_2987_ = !lean_is_exclusive(v___x_2964_);
if (v_isSharedCheck_2987_ == 0)
{
v___x_2968_ = v___x_2964_;
v_isShared_2969_ = v_isSharedCheck_2987_;
goto v_resetjp_2967_;
}
else
{
lean_inc(v_a_2966_);
lean_inc(v_a_2965_);
lean_dec(v___x_2964_);
v___x_2968_ = lean_box(0);
v_isShared_2969_ = v_isSharedCheck_2987_;
goto v_resetjp_2967_;
}
v_resetjp_2967_:
{
lean_object* v_quotContext_2970_; lean_object* v_currMacroScope_2971_; lean_object* v_ref_2972_; uint8_t v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2985_; 
v_quotContext_2970_ = lean_ctor_get(v_a_1712_, 1);
v_currMacroScope_2971_ = lean_ctor_get(v_a_1712_, 2);
v_ref_2972_ = lean_ctor_get(v_a_1712_, 5);
v___x_2973_ = 0;
v___x_2974_ = l_Lean_SourceInfo_fromRef(v_ref_2972_, v___x_2973_);
v___x_2975_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4));
v___x_2976_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__285, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__285_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__285);
v___x_2977_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__287));
lean_inc(v_currMacroScope_2971_);
lean_inc(v_quotContext_2970_);
v___x_2978_ = l_Lean_addMacroScope(v_quotContext_2970_, v___x_2977_, v_currMacroScope_2971_);
v___x_2979_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__291));
lean_inc_n(v___x_2974_, 2);
v___x_2980_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2980_, 0, v___x_2974_);
lean_ctor_set(v___x_2980_, 1, v___x_2976_);
lean_ctor_set(v___x_2980_, 2, v___x_2978_);
lean_ctor_set(v___x_2980_, 3, v___x_2979_);
v___x_2981_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15));
v___x_2982_ = l_Lean_Syntax_node1(v___x_2974_, v___x_2981_, v_a_2965_);
v___x_2983_ = l_Lean_Syntax_node2(v___x_2974_, v___x_2975_, v___x_2980_, v___x_2982_);
if (v_isShared_2969_ == 0)
{
lean_ctor_set(v___x_2968_, 0, v___x_2983_);
v___x_2985_ = v___x_2968_;
goto v_reusejp_2984_;
}
else
{
lean_object* v_reuseFailAlloc_2986_; 
v_reuseFailAlloc_2986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2986_, 0, v___x_2983_);
lean_ctor_set(v_reuseFailAlloc_2986_, 1, v_a_2966_);
v___x_2985_ = v_reuseFailAlloc_2986_;
goto v_reusejp_2984_;
}
v_reusejp_2984_:
{
return v___x_2985_;
}
}
}
case 32:
{
uint8_t v_presentation_2988_; lean_object* v___x_2989_; lean_object* v_a_2990_; lean_object* v_a_2991_; lean_object* v___x_2993_; uint8_t v_isShared_2994_; uint8_t v_isSharedCheck_3012_; 
v_presentation_2988_ = lean_ctor_get_uint8(v_x_1711_, 0);
lean_dec_ref_known(v_x_1711_, 0);
v___x_2989_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO(v_presentation_2988_, v_a_1712_, v_a_1713_);
v_a_2990_ = lean_ctor_get(v___x_2989_, 0);
v_a_2991_ = lean_ctor_get(v___x_2989_, 1);
v_isSharedCheck_3012_ = !lean_is_exclusive(v___x_2989_);
if (v_isSharedCheck_3012_ == 0)
{
v___x_2993_ = v___x_2989_;
v_isShared_2994_ = v_isSharedCheck_3012_;
goto v_resetjp_2992_;
}
else
{
lean_inc(v_a_2991_);
lean_inc(v_a_2990_);
lean_dec(v___x_2989_);
v___x_2993_ = lean_box(0);
v_isShared_2994_ = v_isSharedCheck_3012_;
goto v_resetjp_2992_;
}
v_resetjp_2992_:
{
lean_object* v_quotContext_2995_; lean_object* v_currMacroScope_2996_; lean_object* v_ref_2997_; uint8_t v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3010_; 
v_quotContext_2995_ = lean_ctor_get(v_a_1712_, 1);
v_currMacroScope_2996_ = lean_ctor_get(v_a_1712_, 2);
v_ref_2997_ = lean_ctor_get(v_a_1712_, 5);
v___x_2998_ = 0;
v___x_2999_ = l_Lean_SourceInfo_fromRef(v_ref_2997_, v___x_2998_);
v___x_3000_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4));
v___x_3001_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__293, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__293_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__293);
v___x_3002_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__295));
lean_inc(v_currMacroScope_2996_);
lean_inc(v_quotContext_2995_);
v___x_3003_ = l_Lean_addMacroScope(v_quotContext_2995_, v___x_3002_, v_currMacroScope_2996_);
v___x_3004_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__299));
lean_inc_n(v___x_2999_, 2);
v___x_3005_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3005_, 0, v___x_2999_);
lean_ctor_set(v___x_3005_, 1, v___x_3001_);
lean_ctor_set(v___x_3005_, 2, v___x_3003_);
lean_ctor_set(v___x_3005_, 3, v___x_3004_);
v___x_3006_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15));
v___x_3007_ = l_Lean_Syntax_node1(v___x_2999_, v___x_3006_, v_a_2990_);
v___x_3008_ = l_Lean_Syntax_node2(v___x_2999_, v___x_3000_, v___x_3005_, v___x_3007_);
if (v_isShared_2994_ == 0)
{
lean_ctor_set(v___x_2993_, 0, v___x_3008_);
v___x_3010_ = v___x_2993_;
goto v_reusejp_3009_;
}
else
{
lean_object* v_reuseFailAlloc_3011_; 
v_reuseFailAlloc_3011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3011_, 0, v___x_3008_);
lean_ctor_set(v_reuseFailAlloc_3011_, 1, v_a_2991_);
v___x_3010_ = v_reuseFailAlloc_3011_;
goto v_reusejp_3009_;
}
v_reusejp_3009_:
{
return v___x_3010_;
}
}
}
case 33:
{
uint8_t v_presentation_3013_; lean_object* v___x_3014_; lean_object* v_a_3015_; lean_object* v_a_3016_; lean_object* v___x_3018_; uint8_t v_isShared_3019_; uint8_t v_isSharedCheck_3037_; 
v_presentation_3013_ = lean_ctor_get_uint8(v_x_1711_, 0);
lean_dec_ref_known(v_x_1711_, 0);
v___x_3014_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX(v_presentation_3013_, v_a_1712_, v_a_1713_);
v_a_3015_ = lean_ctor_get(v___x_3014_, 0);
v_a_3016_ = lean_ctor_get(v___x_3014_, 1);
v_isSharedCheck_3037_ = !lean_is_exclusive(v___x_3014_);
if (v_isSharedCheck_3037_ == 0)
{
v___x_3018_ = v___x_3014_;
v_isShared_3019_ = v_isSharedCheck_3037_;
goto v_resetjp_3017_;
}
else
{
lean_inc(v_a_3016_);
lean_inc(v_a_3015_);
lean_dec(v___x_3014_);
v___x_3018_ = lean_box(0);
v_isShared_3019_ = v_isSharedCheck_3037_;
goto v_resetjp_3017_;
}
v_resetjp_3017_:
{
lean_object* v_quotContext_3020_; lean_object* v_currMacroScope_3021_; lean_object* v_ref_3022_; uint8_t v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3035_; 
v_quotContext_3020_ = lean_ctor_get(v_a_1712_, 1);
v_currMacroScope_3021_ = lean_ctor_get(v_a_1712_, 2);
v_ref_3022_ = lean_ctor_get(v_a_1712_, 5);
v___x_3023_ = 0;
v___x_3024_ = l_Lean_SourceInfo_fromRef(v_ref_3022_, v___x_3023_);
v___x_3025_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4));
v___x_3026_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__301, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__301_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__301);
v___x_3027_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__303));
lean_inc(v_currMacroScope_3021_);
lean_inc(v_quotContext_3020_);
v___x_3028_ = l_Lean_addMacroScope(v_quotContext_3020_, v___x_3027_, v_currMacroScope_3021_);
v___x_3029_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__307));
lean_inc_n(v___x_3024_, 2);
v___x_3030_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3030_, 0, v___x_3024_);
lean_ctor_set(v___x_3030_, 1, v___x_3026_);
lean_ctor_set(v___x_3030_, 2, v___x_3028_);
lean_ctor_set(v___x_3030_, 3, v___x_3029_);
v___x_3031_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15));
v___x_3032_ = l_Lean_Syntax_node1(v___x_3024_, v___x_3031_, v_a_3015_);
v___x_3033_ = l_Lean_Syntax_node2(v___x_3024_, v___x_3025_, v___x_3030_, v___x_3032_);
if (v_isShared_3019_ == 0)
{
lean_ctor_set(v___x_3018_, 0, v___x_3033_);
v___x_3035_ = v___x_3018_;
goto v_reusejp_3034_;
}
else
{
lean_object* v_reuseFailAlloc_3036_; 
v_reuseFailAlloc_3036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3036_, 0, v___x_3033_);
lean_ctor_set(v_reuseFailAlloc_3036_, 1, v_a_3016_);
v___x_3035_ = v_reuseFailAlloc_3036_;
goto v_reusejp_3034_;
}
v_reusejp_3034_:
{
return v___x_3035_;
}
}
}
case 34:
{
uint8_t v_presentation_3038_; lean_object* v___x_3039_; lean_object* v_a_3040_; lean_object* v_a_3041_; lean_object* v___x_3043_; uint8_t v_isShared_3044_; uint8_t v_isSharedCheck_3062_; 
v_presentation_3038_ = lean_ctor_get_uint8(v_x_1711_, 0);
lean_dec_ref_known(v_x_1711_, 0);
v___x_3039_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX(v_presentation_3038_, v_a_1712_, v_a_1713_);
v_a_3040_ = lean_ctor_get(v___x_3039_, 0);
v_a_3041_ = lean_ctor_get(v___x_3039_, 1);
v_isSharedCheck_3062_ = !lean_is_exclusive(v___x_3039_);
if (v_isSharedCheck_3062_ == 0)
{
v___x_3043_ = v___x_3039_;
v_isShared_3044_ = v_isSharedCheck_3062_;
goto v_resetjp_3042_;
}
else
{
lean_inc(v_a_3041_);
lean_inc(v_a_3040_);
lean_dec(v___x_3039_);
v___x_3043_ = lean_box(0);
v_isShared_3044_ = v_isSharedCheck_3062_;
goto v_resetjp_3042_;
}
v_resetjp_3042_:
{
lean_object* v_quotContext_3045_; lean_object* v_currMacroScope_3046_; lean_object* v_ref_3047_; uint8_t v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3060_; 
v_quotContext_3045_ = lean_ctor_get(v_a_1712_, 1);
v_currMacroScope_3046_ = lean_ctor_get(v_a_1712_, 2);
v_ref_3047_ = lean_ctor_get(v_a_1712_, 5);
v___x_3048_ = 0;
v___x_3049_ = l_Lean_SourceInfo_fromRef(v_ref_3047_, v___x_3048_);
v___x_3050_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4));
v___x_3051_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__309, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__309_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__309);
v___x_3052_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__311));
lean_inc(v_currMacroScope_3046_);
lean_inc(v_quotContext_3045_);
v___x_3053_ = l_Lean_addMacroScope(v_quotContext_3045_, v___x_3052_, v_currMacroScope_3046_);
v___x_3054_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__315));
lean_inc_n(v___x_3049_, 2);
v___x_3055_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3055_, 0, v___x_3049_);
lean_ctor_set(v___x_3055_, 1, v___x_3051_);
lean_ctor_set(v___x_3055_, 2, v___x_3053_);
lean_ctor_set(v___x_3055_, 3, v___x_3054_);
v___x_3056_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15));
v___x_3057_ = l_Lean_Syntax_node1(v___x_3049_, v___x_3056_, v_a_3040_);
v___x_3058_ = l_Lean_Syntax_node2(v___x_3049_, v___x_3050_, v___x_3055_, v___x_3057_);
if (v_isShared_3044_ == 0)
{
lean_ctor_set(v___x_3043_, 0, v___x_3058_);
v___x_3060_ = v___x_3043_;
goto v_reusejp_3059_;
}
else
{
lean_object* v_reuseFailAlloc_3061_; 
v_reuseFailAlloc_3061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3061_, 0, v___x_3058_);
lean_ctor_set(v_reuseFailAlloc_3061_, 1, v_a_3041_);
v___x_3060_ = v_reuseFailAlloc_3061_;
goto v_reusejp_3059_;
}
v_reusejp_3059_:
{
return v___x_3060_;
}
}
}
default: 
{
uint8_t v_presentation_3063_; lean_object* v___x_3064_; lean_object* v_a_3065_; lean_object* v_a_3066_; lean_object* v___x_3068_; uint8_t v_isShared_3069_; uint8_t v_isSharedCheck_3087_; 
v_presentation_3063_ = lean_ctor_get_uint8(v_x_1711_, 0);
lean_dec_ref_known(v_x_1711_, 0);
v___x_3064_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ(v_presentation_3063_, v_a_1712_, v_a_1713_);
v_a_3065_ = lean_ctor_get(v___x_3064_, 0);
v_a_3066_ = lean_ctor_get(v___x_3064_, 1);
v_isSharedCheck_3087_ = !lean_is_exclusive(v___x_3064_);
if (v_isSharedCheck_3087_ == 0)
{
v___x_3068_ = v___x_3064_;
v_isShared_3069_ = v_isSharedCheck_3087_;
goto v_resetjp_3067_;
}
else
{
lean_inc(v_a_3066_);
lean_inc(v_a_3065_);
lean_dec(v___x_3064_);
v___x_3068_ = lean_box(0);
v_isShared_3069_ = v_isSharedCheck_3087_;
goto v_resetjp_3067_;
}
v_resetjp_3067_:
{
lean_object* v_quotContext_3070_; lean_object* v_currMacroScope_3071_; lean_object* v_ref_3072_; uint8_t v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3085_; 
v_quotContext_3070_ = lean_ctor_get(v_a_1712_, 1);
v_currMacroScope_3071_ = lean_ctor_get(v_a_1712_, 2);
v_ref_3072_ = lean_ctor_get(v_a_1712_, 5);
v___x_3073_ = 0;
v___x_3074_ = l_Lean_SourceInfo_fromRef(v_ref_3072_, v___x_3073_);
v___x_3075_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4));
v___x_3076_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__317, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__317_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__317);
v___x_3077_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__319));
lean_inc(v_currMacroScope_3071_);
lean_inc(v_quotContext_3070_);
v___x_3078_ = l_Lean_addMacroScope(v_quotContext_3070_, v___x_3077_, v_currMacroScope_3071_);
v___x_3079_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__323));
lean_inc_n(v___x_3074_, 2);
v___x_3080_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3080_, 0, v___x_3074_);
lean_ctor_set(v___x_3080_, 1, v___x_3076_);
lean_ctor_set(v___x_3080_, 2, v___x_3078_);
lean_ctor_set(v___x_3080_, 3, v___x_3079_);
v___x_3081_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15));
v___x_3082_ = l_Lean_Syntax_node1(v___x_3074_, v___x_3081_, v_a_3065_);
v___x_3083_ = l_Lean_Syntax_node2(v___x_3074_, v___x_3075_, v___x_3080_, v___x_3082_);
if (v_isShared_3069_ == 0)
{
lean_ctor_set(v___x_3068_, 0, v___x_3083_);
v___x_3085_ = v___x_3068_;
goto v_reusejp_3084_;
}
else
{
lean_object* v_reuseFailAlloc_3086_; 
v_reuseFailAlloc_3086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3086_, 0, v___x_3083_);
lean_ctor_set(v_reuseFailAlloc_3086_, 1, v_a_3066_);
v___x_3085_ = v_reuseFailAlloc_3086_;
goto v_reusejp_3084_;
}
v_reusejp_3084_:
{
return v___x_3085_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___boxed(lean_object* v_x_3088_, lean_object* v_a_3089_, lean_object* v_a_3090_){
_start:
{
lean_object* v_res_3091_; 
v_res_3091_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier(v_x_3088_, v_a_3089_, v_a_3090_);
lean_dec_ref(v_a_3089_);
return v_res_3091_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertFormatPart___closed__1(void){
_start:
{
lean_object* v___x_3093_; lean_object* v___x_3094_; 
v___x_3093_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertFormatPart___closed__0));
v___x_3094_ = l_String_toRawSubstring_x27(v___x_3093_);
return v___x_3094_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertFormatPart___closed__4(void){
_start:
{
lean_object* v___x_3098_; lean_object* v___x_3099_; 
v___x_3098_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertFormatPart___closed__3));
v___x_3099_ = l_String_toRawSubstring_x27(v___x_3098_);
return v___x_3099_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertFormatPart(lean_object* v_x_3102_, lean_object* v_a_3103_, lean_object* v_a_3104_){
_start:
{
if (lean_obj_tag(v_x_3102_) == 0)
{
lean_object* v_val_3105_; lean_object* v_quotContext_3106_; lean_object* v_currMacroScope_3107_; lean_object* v_ref_3108_; uint8_t v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; 
v_val_3105_ = lean_ctor_get(v_x_3102_, 0);
lean_inc_ref(v_val_3105_);
lean_dec_ref_known(v_x_3102_, 1);
v_quotContext_3106_ = lean_ctor_get(v_a_3103_, 1);
v_currMacroScope_3107_ = lean_ctor_get(v_a_3103_, 2);
v_ref_3108_ = lean_ctor_get(v_a_3103_, 5);
v___x_3109_ = 0;
v___x_3110_ = l_Lean_SourceInfo_fromRef(v_ref_3108_, v___x_3109_);
v___x_3111_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4));
v___x_3112_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__67));
v___x_3113_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__68));
lean_inc_n(v___x_3110_, 4);
v___x_3114_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3114_, 0, v___x_3110_);
lean_ctor_set(v___x_3114_, 1, v___x_3113_);
v___x_3115_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertFormatPart___closed__1, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertFormatPart___closed__1_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertFormatPart___closed__1);
v___x_3116_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertFormatPart___closed__2));
lean_inc(v_currMacroScope_3107_);
lean_inc(v_quotContext_3106_);
v___x_3117_ = l_Lean_addMacroScope(v_quotContext_3106_, v___x_3116_, v_currMacroScope_3107_);
v___x_3118_ = lean_box(0);
v___x_3119_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3119_, 0, v___x_3110_);
lean_ctor_set(v___x_3119_, 1, v___x_3115_);
lean_ctor_set(v___x_3119_, 2, v___x_3117_);
lean_ctor_set(v___x_3119_, 3, v___x_3118_);
v___x_3120_ = l_Lean_Syntax_node2(v___x_3110_, v___x_3112_, v___x_3114_, v___x_3119_);
v___x_3121_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15));
v___x_3122_ = lean_box(2);
v___x_3123_ = l_Lean_Syntax_mkStrLit(v_val_3105_, v___x_3122_);
v___x_3124_ = l_Lean_Syntax_node1(v___x_3110_, v___x_3121_, v___x_3123_);
v___x_3125_ = l_Lean_Syntax_node2(v___x_3110_, v___x_3111_, v___x_3120_, v___x_3124_);
v___x_3126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3126_, 0, v___x_3125_);
lean_ctor_set(v___x_3126_, 1, v_a_3104_);
return v___x_3126_;
}
else
{
lean_object* v_modifier_3127_; lean_object* v___x_3128_; lean_object* v_a_3129_; lean_object* v_a_3130_; lean_object* v___x_3132_; uint8_t v_isShared_3133_; uint8_t v_isSharedCheck_3155_; 
v_modifier_3127_ = lean_ctor_get(v_x_3102_, 0);
lean_inc_ref(v_modifier_3127_);
lean_dec_ref_known(v_x_3102_, 1);
v___x_3128_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier(v_modifier_3127_, v_a_3103_, v_a_3104_);
v_a_3129_ = lean_ctor_get(v___x_3128_, 0);
v_a_3130_ = lean_ctor_get(v___x_3128_, 1);
v_isSharedCheck_3155_ = !lean_is_exclusive(v___x_3128_);
if (v_isSharedCheck_3155_ == 0)
{
v___x_3132_ = v___x_3128_;
v_isShared_3133_ = v_isSharedCheck_3155_;
goto v_resetjp_3131_;
}
else
{
lean_inc(v_a_3130_);
lean_inc(v_a_3129_);
lean_dec(v___x_3128_);
v___x_3132_ = lean_box(0);
v_isShared_3133_ = v_isSharedCheck_3155_;
goto v_resetjp_3131_;
}
v_resetjp_3131_:
{
lean_object* v_quotContext_3134_; lean_object* v_currMacroScope_3135_; lean_object* v_ref_3136_; uint8_t v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3153_; 
v_quotContext_3134_ = lean_ctor_get(v_a_3103_, 1);
v_currMacroScope_3135_ = lean_ctor_get(v_a_3103_, 2);
v_ref_3136_ = lean_ctor_get(v_a_3103_, 5);
v___x_3137_ = 0;
v___x_3138_ = l_Lean_SourceInfo_fromRef(v_ref_3136_, v___x_3137_);
v___x_3139_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4));
v___x_3140_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__67));
v___x_3141_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__68));
lean_inc_n(v___x_3138_, 4);
v___x_3142_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3142_, 0, v___x_3138_);
lean_ctor_set(v___x_3142_, 1, v___x_3141_);
v___x_3143_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_convertFormatPart___closed__4, &l___private_Std_Time_Notation_Spec_0__Std_Time_convertFormatPart___closed__4_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertFormatPart___closed__4);
v___x_3144_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertFormatPart___closed__5));
lean_inc(v_currMacroScope_3135_);
lean_inc(v_quotContext_3134_);
v___x_3145_ = l_Lean_addMacroScope(v_quotContext_3134_, v___x_3144_, v_currMacroScope_3135_);
v___x_3146_ = lean_box(0);
v___x_3147_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3147_, 0, v___x_3138_);
lean_ctor_set(v___x_3147_, 1, v___x_3143_);
lean_ctor_set(v___x_3147_, 2, v___x_3145_);
lean_ctor_set(v___x_3147_, 3, v___x_3146_);
v___x_3148_ = l_Lean_Syntax_node2(v___x_3138_, v___x_3140_, v___x_3142_, v___x_3147_);
v___x_3149_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15));
v___x_3150_ = l_Lean_Syntax_node1(v___x_3138_, v___x_3149_, v_a_3129_);
v___x_3151_ = l_Lean_Syntax_node2(v___x_3138_, v___x_3139_, v___x_3148_, v___x_3150_);
if (v_isShared_3133_ == 0)
{
lean_ctor_set(v___x_3132_, 0, v___x_3151_);
v___x_3153_ = v___x_3132_;
goto v_reusejp_3152_;
}
else
{
lean_object* v_reuseFailAlloc_3154_; 
v_reuseFailAlloc_3154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3154_, 0, v___x_3151_);
lean_ctor_set(v_reuseFailAlloc_3154_, 1, v_a_3130_);
v___x_3153_ = v_reuseFailAlloc_3154_;
goto v_reusejp_3152_;
}
v_reusejp_3152_:
{
return v___x_3153_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_convertFormatPart___boxed(lean_object* v_x_3156_, lean_object* v_a_3157_, lean_object* v_a_3158_){
_start:
{
lean_object* v_res_3159_; 
v_res_3159_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertFormatPart(v_x_3156_, v_a_3157_, v_a_3158_);
lean_dec_ref(v_a_3157_);
return v_res_3159_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat_spec__1(lean_object* v_x_3222_, lean_object* v_x_3223_){
_start:
{
if (lean_obj_tag(v_x_3223_) == 0)
{
return v_x_3222_;
}
else
{
lean_object* v_head_3224_; lean_object* v_tail_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; 
v_head_3224_ = lean_ctor_get(v_x_3223_, 0);
lean_inc(v_head_3224_);
v_tail_3225_ = lean_ctor_get(v_x_3223_, 1);
lean_inc(v_tail_3225_);
lean_dec_ref_known(v_x_3223_, 2);
v___x_3226_ = ((lean_object*)(l_Std_Time_termDatespec_x28___x2c___x29___closed__2));
v___x_3227_ = l_Lean_Syntax_TSepArray_push___redArg(v___x_3226_, v_x_3222_, v_head_3224_);
v_x_3222_ = v___x_3227_;
v_x_3223_ = v_tail_3225_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat_spec__0(lean_object* v_x_3229_, lean_object* v_x_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_){
_start:
{
if (lean_obj_tag(v_x_3229_) == 0)
{
lean_object* v___x_3233_; lean_object* v___x_3234_; 
v___x_3233_ = l_List_reverse___redArg(v_x_3230_);
v___x_3234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3234_, 0, v___x_3233_);
lean_ctor_set(v___x_3234_, 1, v___y_3232_);
return v___x_3234_;
}
else
{
lean_object* v_head_3235_; lean_object* v_tail_3236_; lean_object* v___x_3238_; uint8_t v_isShared_3239_; uint8_t v_isSharedCheck_3247_; 
v_head_3235_ = lean_ctor_get(v_x_3229_, 0);
v_tail_3236_ = lean_ctor_get(v_x_3229_, 1);
v_isSharedCheck_3247_ = !lean_is_exclusive(v_x_3229_);
if (v_isSharedCheck_3247_ == 0)
{
v___x_3238_ = v_x_3229_;
v_isShared_3239_ = v_isSharedCheck_3247_;
goto v_resetjp_3237_;
}
else
{
lean_inc(v_tail_3236_);
lean_inc(v_head_3235_);
lean_dec(v_x_3229_);
v___x_3238_ = lean_box(0);
v_isShared_3239_ = v_isSharedCheck_3247_;
goto v_resetjp_3237_;
}
v_resetjp_3237_:
{
lean_object* v___x_3240_; lean_object* v_a_3241_; lean_object* v_a_3242_; lean_object* v___x_3244_; 
v___x_3240_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertFormatPart(v_head_3235_, v___y_3231_, v___y_3232_);
v_a_3241_ = lean_ctor_get(v___x_3240_, 0);
lean_inc(v_a_3241_);
v_a_3242_ = lean_ctor_get(v___x_3240_, 1);
lean_inc(v_a_3242_);
lean_dec_ref(v___x_3240_);
if (v_isShared_3239_ == 0)
{
lean_ctor_set(v___x_3238_, 1, v_x_3230_);
lean_ctor_set(v___x_3238_, 0, v_a_3241_);
v___x_3244_ = v___x_3238_;
goto v_reusejp_3243_;
}
else
{
lean_object* v_reuseFailAlloc_3246_; 
v_reuseFailAlloc_3246_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3246_, 0, v_a_3241_);
lean_ctor_set(v_reuseFailAlloc_3246_, 1, v_x_3230_);
v___x_3244_ = v_reuseFailAlloc_3246_;
goto v_reusejp_3243_;
}
v_reusejp_3243_:
{
v_x_3229_ = v_tail_3236_;
v_x_3230_ = v___x_3244_;
v___y_3232_ = v_a_3242_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat_spec__0___boxed(lean_object* v_x_3248_, lean_object* v_x_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_){
_start:
{
lean_object* v_res_3252_; 
v_res_3252_ = l_List_mapM_loop___at___00__private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat_spec__0(v_x_3248_, v_x_3249_, v___y_3250_, v___y_3251_);
lean_dec_ref(v___y_3250_);
return v_res_3252_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__0(void){
_start:
{
lean_object* v___x_3253_; uint8_t v___x_3254_; lean_object* v___x_3255_; 
v___x_3253_ = l_Std_Time_DateFormat_enUS;
v___x_3254_ = 0;
v___x_3255_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3255_, 0, v___x_3253_);
lean_ctor_set_uint8(v___x_3255_, sizeof(void*)*1, v___x_3254_);
return v___x_3255_;
}
}
static lean_object* _init_l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__9(void){
_start:
{
lean_object* v___x_3270_; 
v___x_3270_ = l_Array_mkArray0(lean_box(0));
return v___x_3270_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat(lean_object* v_fmt_3299_, lean_object* v_config_3300_, lean_object* v_a_3301_, lean_object* v_a_3302_){
_start:
{
lean_object* v_input_3303_; uint8_t v___x_3304_; lean_object* v___x_3305_; lean_object* v_format_3306_; 
v_input_3303_ = l_Lean_TSyntax_getString(v_fmt_3299_);
v___x_3304_ = 0;
v___x_3305_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__0, &l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__0_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__0);
v_format_3306_ = l_Std_Time_GenericFormat_spec___redArg(v_input_3303_, v___x_3305_);
if (lean_obj_tag(v_format_3306_) == 0)
{
lean_object* v_a_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; 
lean_dec(v_config_3300_);
v_a_3307_ = lean_ctor_get(v_format_3306_, 0);
lean_inc(v_a_3307_);
lean_dec_ref_known(v_format_3306_, 1);
v___x_3308_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__1));
v___x_3309_ = lean_string_append(v___x_3308_, v_a_3307_);
lean_dec(v_a_3307_);
v___x_3310_ = l_Lean_Macro_throwErrorAt___redArg(v_fmt_3299_, v___x_3309_, v_a_3301_, v_a_3302_);
return v___x_3310_;
}
else
{
lean_object* v_a_3311_; lean_object* v_string_3312_; lean_object* v___x_3314_; uint8_t v_isShared_3315_; uint8_t v_isSharedCheck_3382_; 
v_a_3311_ = lean_ctor_get(v_format_3306_, 0);
lean_inc(v_a_3311_);
lean_dec_ref_known(v_format_3306_, 1);
v_string_3312_ = lean_ctor_get(v_a_3311_, 1);
v_isSharedCheck_3382_ = !lean_is_exclusive(v_a_3311_);
if (v_isSharedCheck_3382_ == 0)
{
lean_object* v_unused_3383_; 
v_unused_3383_ = lean_ctor_get(v_a_3311_, 0);
lean_dec(v_unused_3383_);
v___x_3314_ = v_a_3311_;
v_isShared_3315_ = v_isSharedCheck_3382_;
goto v_resetjp_3313_;
}
else
{
lean_inc(v_string_3312_);
lean_dec(v_a_3311_);
v___x_3314_ = lean_box(0);
v_isShared_3315_ = v_isSharedCheck_3382_;
goto v_resetjp_3313_;
}
v_resetjp_3313_:
{
lean_object* v___x_3316_; lean_object* v___x_3317_; 
v___x_3316_ = lean_box(0);
v___x_3317_ = l_List_mapM_loop___at___00__private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat_spec__0(v_string_3312_, v___x_3316_, v_a_3301_, v_a_3302_);
if (lean_obj_tag(v___x_3317_) == 0)
{
lean_object* v_a_3318_; lean_object* v_a_3319_; lean_object* v___x_3321_; uint8_t v_isShared_3322_; uint8_t v_isSharedCheck_3372_; 
v_a_3318_ = lean_ctor_get(v___x_3317_, 0);
v_a_3319_ = lean_ctor_get(v___x_3317_, 1);
v_isSharedCheck_3372_ = !lean_is_exclusive(v___x_3317_);
if (v_isSharedCheck_3372_ == 0)
{
v___x_3321_ = v___x_3317_;
v_isShared_3322_ = v_isSharedCheck_3372_;
goto v_resetjp_3320_;
}
else
{
lean_inc(v_a_3319_);
lean_inc(v_a_3318_);
lean_dec(v___x_3317_);
v___x_3321_ = lean_box(0);
v_isShared_3322_ = v_isSharedCheck_3372_;
goto v_resetjp_3320_;
}
v_resetjp_3320_:
{
lean_object* v_ref_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___y_3328_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; 
v_ref_3323_ = lean_ctor_get(v_a_3301_, 5);
v___x_3324_ = ((lean_object*)(l_Std_Time_termDatespec_x28___x2c___x29___closed__2));
v___x_3325_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__2));
v___x_3326_ = l_List_foldl___at___00__private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat_spec__1(v___x_3325_, v_a_3318_);
v___x_3353_ = l_Lean_SourceInfo_fromRef(v_ref_3323_, v___x_3304_);
v___x_3354_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__13));
v___x_3355_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__14));
lean_inc_n(v___x_3353_, 7);
v___x_3356_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3356_, 0, v___x_3353_);
lean_ctor_set(v___x_3356_, 1, v___x_3355_);
v___x_3357_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__15));
v___x_3358_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3358_, 0, v___x_3353_);
lean_ctor_set(v___x_3358_, 1, v___x_3357_);
lean_inc_ref(v___x_3358_);
lean_inc_ref(v___x_3356_);
v___x_3359_ = l_Lean_Syntax_node2(v___x_3353_, v___x_3354_, v___x_3356_, v___x_3358_);
v___x_3360_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__17));
v___x_3361_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15));
v___x_3362_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__9, &l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__9_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__9);
v___x_3363_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3363_, 0, v___x_3353_);
lean_ctor_set(v___x_3363_, 1, v___x_3361_);
lean_ctor_set(v___x_3363_, 2, v___x_3362_);
v___x_3364_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__19));
lean_inc_ref_n(v___x_3363_, 3);
v___x_3365_ = l_Lean_Syntax_node1(v___x_3353_, v___x_3364_, v___x_3363_);
v___x_3366_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__21));
v___x_3367_ = l_Lean_Syntax_node1(v___x_3353_, v___x_3366_, v___x_3363_);
v___x_3368_ = l_Lean_Syntax_node6(v___x_3353_, v___x_3360_, v___x_3356_, v___x_3363_, v___x_3365_, v___x_3367_, v___x_3363_, v___x_3358_);
if (lean_obj_tag(v_config_3300_) == 0)
{
lean_object* v___x_3369_; lean_object* v___x_3370_; 
v___x_3369_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__23));
v___x_3370_ = l_Lean_Syntax_node2(v___x_3353_, v___x_3369_, v___x_3359_, v___x_3368_);
v___y_3328_ = v___x_3370_;
goto v___jp_3327_;
}
else
{
lean_object* v_val_3371_; 
lean_dec(v___x_3368_);
lean_dec(v___x_3359_);
lean_dec(v___x_3353_);
v_val_3371_ = lean_ctor_get(v_config_3300_, 0);
lean_inc(v_val_3371_);
lean_dec_ref_known(v_config_3300_, 1);
v___y_3328_ = v_val_3371_;
goto v___jp_3327_;
}
v___jp_3327_:
{
lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3333_; 
v___x_3329_ = l_Lean_SourceInfo_fromRef(v_ref_3323_, v___x_3304_);
v___x_3330_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__4));
v___x_3331_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__5));
lean_inc(v___x_3329_);
if (v_isShared_3315_ == 0)
{
lean_ctor_set_tag(v___x_3314_, 2);
lean_ctor_set(v___x_3314_, 1, v___x_3331_);
lean_ctor_set(v___x_3314_, 0, v___x_3329_);
v___x_3333_ = v___x_3314_;
goto v_reusejp_3332_;
}
else
{
lean_object* v_reuseFailAlloc_3352_; 
v_reuseFailAlloc_3352_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3352_, 0, v___x_3329_);
lean_ctor_set(v_reuseFailAlloc_3352_, 1, v___x_3331_);
v___x_3333_ = v_reuseFailAlloc_3352_;
goto v_reusejp_3332_;
}
v_reusejp_3332_:
{
lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3350_; 
v___x_3334_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15));
lean_inc_n(v___x_3329_, 7);
v___x_3335_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3335_, 0, v___x_3329_);
lean_ctor_set(v___x_3335_, 1, v___x_3324_);
v___x_3336_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__7));
v___x_3337_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__8));
v___x_3338_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3338_, 0, v___x_3329_);
lean_ctor_set(v___x_3338_, 1, v___x_3337_);
v___x_3339_ = lean_obj_once(&l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__9, &l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__9_once, _init_l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__9);
v___x_3340_ = l_Array_append___redArg(v___x_3339_, v___x_3326_);
lean_dec_ref(v___x_3326_);
v___x_3341_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3341_, 0, v___x_3329_);
lean_ctor_set(v___x_3341_, 1, v___x_3334_);
lean_ctor_set(v___x_3341_, 2, v___x_3340_);
v___x_3342_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__10));
v___x_3343_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3343_, 0, v___x_3329_);
lean_ctor_set(v___x_3343_, 1, v___x_3342_);
v___x_3344_ = l_Lean_Syntax_node3(v___x_3329_, v___x_3336_, v___x_3338_, v___x_3341_, v___x_3343_);
v___x_3345_ = l_Lean_Syntax_node3(v___x_3329_, v___x_3334_, v___y_3328_, v___x_3335_, v___x_3344_);
v___x_3346_ = ((lean_object*)(l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__11));
v___x_3347_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3347_, 0, v___x_3329_);
lean_ctor_set(v___x_3347_, 1, v___x_3346_);
v___x_3348_ = l_Lean_Syntax_node3(v___x_3329_, v___x_3330_, v___x_3333_, v___x_3345_, v___x_3347_);
if (v_isShared_3322_ == 0)
{
lean_ctor_set(v___x_3321_, 0, v___x_3348_);
v___x_3350_ = v___x_3321_;
goto v_reusejp_3349_;
}
else
{
lean_object* v_reuseFailAlloc_3351_; 
v_reuseFailAlloc_3351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3351_, 0, v___x_3348_);
lean_ctor_set(v_reuseFailAlloc_3351_, 1, v_a_3319_);
v___x_3350_ = v_reuseFailAlloc_3351_;
goto v_reusejp_3349_;
}
v_reusejp_3349_:
{
return v___x_3350_;
}
}
}
}
}
else
{
lean_object* v_a_3373_; lean_object* v_a_3374_; lean_object* v___x_3376_; uint8_t v_isShared_3377_; uint8_t v_isSharedCheck_3381_; 
lean_del_object(v___x_3314_);
lean_dec(v_config_3300_);
v_a_3373_ = lean_ctor_get(v___x_3317_, 0);
v_a_3374_ = lean_ctor_get(v___x_3317_, 1);
v_isSharedCheck_3381_ = !lean_is_exclusive(v___x_3317_);
if (v_isSharedCheck_3381_ == 0)
{
v___x_3376_ = v___x_3317_;
v_isShared_3377_ = v_isSharedCheck_3381_;
goto v_resetjp_3375_;
}
else
{
lean_inc(v_a_3374_);
lean_inc(v_a_3373_);
lean_dec(v___x_3317_);
v___x_3376_ = lean_box(0);
v_isShared_3377_ = v_isSharedCheck_3381_;
goto v_resetjp_3375_;
}
v_resetjp_3375_:
{
lean_object* v___x_3379_; 
if (v_isShared_3377_ == 0)
{
v___x_3379_ = v___x_3376_;
goto v_reusejp_3378_;
}
else
{
lean_object* v_reuseFailAlloc_3380_; 
v_reuseFailAlloc_3380_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3380_, 0, v_a_3373_);
lean_ctor_set(v_reuseFailAlloc_3380_, 1, v_a_3374_);
v___x_3379_ = v_reuseFailAlloc_3380_;
goto v_reusejp_3378_;
}
v_reusejp_3378_:
{
return v___x_3379_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___boxed(lean_object* v_fmt_3384_, lean_object* v_config_3385_, lean_object* v_a_3386_, lean_object* v_a_3387_){
_start:
{
lean_object* v_res_3388_; 
v_res_3388_ = l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat(v_fmt_3384_, v_config_3385_, v_a_3386_, v_a_3387_);
lean_dec_ref(v_a_3386_);
lean_dec(v_fmt_3384_);
return v_res_3388_;
}
}
LEAN_EXPORT lean_object* l_Std_Time___aux__Std__Time__Notation__Spec______macroRules__Std__Time__termDatespec_x28___x29__1(lean_object* v_x_3389_, lean_object* v_a_3390_, lean_object* v_a_3391_){
_start:
{
lean_object* v___x_3392_; uint8_t v___x_3393_; 
v___x_3392_ = ((lean_object*)(l_Std_Time_termDatespec_x28___x29___closed__1));
lean_inc(v_x_3389_);
v___x_3393_ = l_Lean_Syntax_isOfKind(v_x_3389_, v___x_3392_);
if (v___x_3393_ == 0)
{
lean_object* v___x_3394_; lean_object* v___x_3395_; 
lean_dec(v_x_3389_);
v___x_3394_ = lean_box(1);
v___x_3395_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3395_, 0, v___x_3394_);
lean_ctor_set(v___x_3395_, 1, v_a_3391_);
return v___x_3395_;
}
else
{
lean_object* v___x_3396_; lean_object* v_fmt_3397_; lean_object* v___x_3398_; uint8_t v___x_3399_; 
v___x_3396_ = lean_unsigned_to_nat(1u);
v_fmt_3397_ = l_Lean_Syntax_getArg(v_x_3389_, v___x_3396_);
lean_dec(v_x_3389_);
v___x_3398_ = ((lean_object*)(l_Std_Time_termDatespec_x28___x29___closed__7));
lean_inc(v_fmt_3397_);
v___x_3399_ = l_Lean_Syntax_isOfKind(v_fmt_3397_, v___x_3398_);
if (v___x_3399_ == 0)
{
lean_object* v___x_3400_; lean_object* v___x_3401_; 
lean_dec(v_fmt_3397_);
v___x_3400_ = lean_box(1);
v___x_3401_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3401_, 0, v___x_3400_);
lean_ctor_set(v___x_3401_, 1, v_a_3391_);
return v___x_3401_;
}
else
{
lean_object* v___x_3402_; lean_object* v___x_3403_; 
v___x_3402_ = lean_box(0);
v___x_3403_ = l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat(v_fmt_3397_, v___x_3402_, v_a_3390_, v_a_3391_);
lean_dec(v_fmt_3397_);
if (lean_obj_tag(v___x_3403_) == 0)
{
lean_object* v_a_3404_; lean_object* v_a_3405_; lean_object* v___x_3407_; uint8_t v_isShared_3408_; uint8_t v_isSharedCheck_3412_; 
v_a_3404_ = lean_ctor_get(v___x_3403_, 0);
v_a_3405_ = lean_ctor_get(v___x_3403_, 1);
v_isSharedCheck_3412_ = !lean_is_exclusive(v___x_3403_);
if (v_isSharedCheck_3412_ == 0)
{
v___x_3407_ = v___x_3403_;
v_isShared_3408_ = v_isSharedCheck_3412_;
goto v_resetjp_3406_;
}
else
{
lean_inc(v_a_3405_);
lean_inc(v_a_3404_);
lean_dec(v___x_3403_);
v___x_3407_ = lean_box(0);
v_isShared_3408_ = v_isSharedCheck_3412_;
goto v_resetjp_3406_;
}
v_resetjp_3406_:
{
lean_object* v___x_3410_; 
if (v_isShared_3408_ == 0)
{
v___x_3410_ = v___x_3407_;
goto v_reusejp_3409_;
}
else
{
lean_object* v_reuseFailAlloc_3411_; 
v_reuseFailAlloc_3411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3411_, 0, v_a_3404_);
lean_ctor_set(v_reuseFailAlloc_3411_, 1, v_a_3405_);
v___x_3410_ = v_reuseFailAlloc_3411_;
goto v_reusejp_3409_;
}
v_reusejp_3409_:
{
return v___x_3410_;
}
}
}
else
{
lean_object* v_a_3413_; lean_object* v_a_3414_; lean_object* v___x_3416_; uint8_t v_isShared_3417_; uint8_t v_isSharedCheck_3421_; 
v_a_3413_ = lean_ctor_get(v___x_3403_, 0);
v_a_3414_ = lean_ctor_get(v___x_3403_, 1);
v_isSharedCheck_3421_ = !lean_is_exclusive(v___x_3403_);
if (v_isSharedCheck_3421_ == 0)
{
v___x_3416_ = v___x_3403_;
v_isShared_3417_ = v_isSharedCheck_3421_;
goto v_resetjp_3415_;
}
else
{
lean_inc(v_a_3414_);
lean_inc(v_a_3413_);
lean_dec(v___x_3403_);
v___x_3416_ = lean_box(0);
v_isShared_3417_ = v_isSharedCheck_3421_;
goto v_resetjp_3415_;
}
v_resetjp_3415_:
{
lean_object* v___x_3419_; 
if (v_isShared_3417_ == 0)
{
v___x_3419_ = v___x_3416_;
goto v_reusejp_3418_;
}
else
{
lean_object* v_reuseFailAlloc_3420_; 
v_reuseFailAlloc_3420_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3420_, 0, v_a_3413_);
lean_ctor_set(v_reuseFailAlloc_3420_, 1, v_a_3414_);
v___x_3419_ = v_reuseFailAlloc_3420_;
goto v_reusejp_3418_;
}
v_reusejp_3418_:
{
return v___x_3419_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time___aux__Std__Time__Notation__Spec______macroRules__Std__Time__termDatespec_x28___x29__1___boxed(lean_object* v_x_3422_, lean_object* v_a_3423_, lean_object* v_a_3424_){
_start:
{
lean_object* v_res_3425_; 
v_res_3425_ = l_Std_Time___aux__Std__Time__Notation__Spec______macroRules__Std__Time__termDatespec_x28___x29__1(v_x_3422_, v_a_3423_, v_a_3424_);
lean_dec_ref(v_a_3423_);
return v_res_3425_;
}
}
LEAN_EXPORT lean_object* l_Std_Time___aux__Std__Time__Notation__Spec______macroRules__Std__Time__termDatespec_x28___x2c___x29__1(lean_object* v_x_3426_, lean_object* v_a_3427_, lean_object* v_a_3428_){
_start:
{
lean_object* v___x_3429_; uint8_t v___x_3430_; 
v___x_3429_ = ((lean_object*)(l_Std_Time_termDatespec_x28___x2c___x29___closed__1));
lean_inc(v_x_3426_);
v___x_3430_ = l_Lean_Syntax_isOfKind(v_x_3426_, v___x_3429_);
if (v___x_3430_ == 0)
{
lean_object* v___x_3431_; lean_object* v___x_3432_; 
lean_dec(v_x_3426_);
v___x_3431_ = lean_box(1);
v___x_3432_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3432_, 0, v___x_3431_);
lean_ctor_set(v___x_3432_, 1, v_a_3428_);
return v___x_3432_;
}
else
{
lean_object* v___x_3433_; lean_object* v_fmt_3434_; lean_object* v___x_3435_; uint8_t v___x_3436_; 
v___x_3433_ = lean_unsigned_to_nat(1u);
v_fmt_3434_ = l_Lean_Syntax_getArg(v_x_3426_, v___x_3433_);
v___x_3435_ = ((lean_object*)(l_Std_Time_termDatespec_x28___x29___closed__7));
lean_inc(v_fmt_3434_);
v___x_3436_ = l_Lean_Syntax_isOfKind(v_fmt_3434_, v___x_3435_);
if (v___x_3436_ == 0)
{
lean_object* v___x_3437_; lean_object* v___x_3438_; 
lean_dec(v_fmt_3434_);
lean_dec(v_x_3426_);
v___x_3437_ = lean_box(1);
v___x_3438_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3438_, 0, v___x_3437_);
lean_ctor_set(v___x_3438_, 1, v_a_3428_);
return v___x_3438_;
}
else
{
lean_object* v___x_3439_; lean_object* v_config_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; 
v___x_3439_ = lean_unsigned_to_nat(3u);
v_config_3440_ = l_Lean_Syntax_getArg(v_x_3426_, v___x_3439_);
lean_dec(v_x_3426_);
v___x_3441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3441_, 0, v_config_3440_);
v___x_3442_ = l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat(v_fmt_3434_, v___x_3441_, v_a_3427_, v_a_3428_);
lean_dec(v_fmt_3434_);
if (lean_obj_tag(v___x_3442_) == 0)
{
lean_object* v_a_3443_; lean_object* v_a_3444_; lean_object* v___x_3446_; uint8_t v_isShared_3447_; uint8_t v_isSharedCheck_3451_; 
v_a_3443_ = lean_ctor_get(v___x_3442_, 0);
v_a_3444_ = lean_ctor_get(v___x_3442_, 1);
v_isSharedCheck_3451_ = !lean_is_exclusive(v___x_3442_);
if (v_isSharedCheck_3451_ == 0)
{
v___x_3446_ = v___x_3442_;
v_isShared_3447_ = v_isSharedCheck_3451_;
goto v_resetjp_3445_;
}
else
{
lean_inc(v_a_3444_);
lean_inc(v_a_3443_);
lean_dec(v___x_3442_);
v___x_3446_ = lean_box(0);
v_isShared_3447_ = v_isSharedCheck_3451_;
goto v_resetjp_3445_;
}
v_resetjp_3445_:
{
lean_object* v___x_3449_; 
if (v_isShared_3447_ == 0)
{
v___x_3449_ = v___x_3446_;
goto v_reusejp_3448_;
}
else
{
lean_object* v_reuseFailAlloc_3450_; 
v_reuseFailAlloc_3450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3450_, 0, v_a_3443_);
lean_ctor_set(v_reuseFailAlloc_3450_, 1, v_a_3444_);
v___x_3449_ = v_reuseFailAlloc_3450_;
goto v_reusejp_3448_;
}
v_reusejp_3448_:
{
return v___x_3449_;
}
}
}
else
{
lean_object* v_a_3452_; lean_object* v_a_3453_; lean_object* v___x_3455_; uint8_t v_isShared_3456_; uint8_t v_isSharedCheck_3460_; 
v_a_3452_ = lean_ctor_get(v___x_3442_, 0);
v_a_3453_ = lean_ctor_get(v___x_3442_, 1);
v_isSharedCheck_3460_ = !lean_is_exclusive(v___x_3442_);
if (v_isSharedCheck_3460_ == 0)
{
v___x_3455_ = v___x_3442_;
v_isShared_3456_ = v_isSharedCheck_3460_;
goto v_resetjp_3454_;
}
else
{
lean_inc(v_a_3453_);
lean_inc(v_a_3452_);
lean_dec(v___x_3442_);
v___x_3455_ = lean_box(0);
v_isShared_3456_ = v_isSharedCheck_3460_;
goto v_resetjp_3454_;
}
v_resetjp_3454_:
{
lean_object* v___x_3458_; 
if (v_isShared_3456_ == 0)
{
v___x_3458_ = v___x_3455_;
goto v_reusejp_3457_;
}
else
{
lean_object* v_reuseFailAlloc_3459_; 
v_reuseFailAlloc_3459_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3459_, 0, v_a_3452_);
lean_ctor_set(v_reuseFailAlloc_3459_, 1, v_a_3453_);
v___x_3458_ = v_reuseFailAlloc_3459_;
goto v_reusejp_3457_;
}
v_reusejp_3457_:
{
return v___x_3458_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time___aux__Std__Time__Notation__Spec______macroRules__Std__Time__termDatespec_x28___x2c___x29__1___boxed(lean_object* v_x_3461_, lean_object* v_a_3462_, lean_object* v_a_3463_){
_start:
{
lean_object* v_res_3464_; 
v_res_3464_ = l_Std_Time___aux__Std__Time__Notation__Spec______macroRules__Std__Time__termDatespec_x28___x2c___x29__1(v_x_3461_, v_a_3462_, v_a_3463_);
lean_dec_ref(v_a_3462_);
return v_res_3464_;
}
}
lean_object* runtime_initialize_Std_Time_Format_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Time_Notation_Spec(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Time_Format_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Std_Time_Format_Basic(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Time_Notation_Spec(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Std_Time_Format_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Time_Format_Basic(uint8_t builtin);
lean_object* initialize_Std_Time_Format_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Time_Notation_Spec(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time_Format_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_Format_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Notation_Spec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Time_Notation_Spec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Time_Notation_Spec(builtin);
}
#ifdef __cplusplus
}
#endif

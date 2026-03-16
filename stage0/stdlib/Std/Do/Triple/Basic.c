// Lean compiler output
// Module: Std.Do.Triple.Basic
// Imports: public import Std.Do.WP
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesIdent(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Do_triple___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Std_Do_triple___closed__0 = (const lean_object*)&l_Std_Do_triple___closed__0_value;
static const lean_string_object l_Std_Do_triple___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l_Std_Do_triple___closed__1 = (const lean_object*)&l_Std_Do_triple___closed__1_value;
static const lean_string_object l_Std_Do_triple___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "triple"};
static const lean_object* l_Std_Do_triple___closed__2 = (const lean_object*)&l_Std_Do_triple___closed__2_value;
static const lean_ctor_object l_Std_Do_triple___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_triple___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Do_triple___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_triple___closed__3_value_aux_0),((lean_object*)&l_Std_Do_triple___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Std_Do_triple___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_triple___closed__3_value_aux_1),((lean_object*)&l_Std_Do_triple___closed__2_value),LEAN_SCALAR_PTR_LITERAL(98, 3, 229, 14, 94, 184, 116, 193)}};
static const lean_object* l_Std_Do_triple___closed__3 = (const lean_object*)&l_Std_Do_triple___closed__3_value;
static const lean_string_object l_Std_Do_triple___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Std_Do_triple___closed__4 = (const lean_object*)&l_Std_Do_triple___closed__4_value;
static const lean_ctor_object l_Std_Do_triple___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_triple___closed__4_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Std_Do_triple___closed__5 = (const lean_object*)&l_Std_Do_triple___closed__5_value;
static const lean_string_object l_Std_Do_triple___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⦃"};
static const lean_object* l_Std_Do_triple___closed__6 = (const lean_object*)&l_Std_Do_triple___closed__6_value;
static const lean_ctor_object l_Std_Do_triple___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Do_triple___closed__6_value)}};
static const lean_object* l_Std_Do_triple___closed__7 = (const lean_object*)&l_Std_Do_triple___closed__7_value;
static const lean_string_object l_Std_Do_triple___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Std_Do_triple___closed__8 = (const lean_object*)&l_Std_Do_triple___closed__8_value;
static const lean_ctor_object l_Std_Do_triple___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_triple___closed__8_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Std_Do_triple___closed__9 = (const lean_object*)&l_Std_Do_triple___closed__9_value;
static const lean_ctor_object l_Std_Do_triple___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Std_Do_triple___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Do_triple___closed__10 = (const lean_object*)&l_Std_Do_triple___closed__10_value;
static const lean_ctor_object l_Std_Do_triple___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Do_triple___closed__5_value),((lean_object*)&l_Std_Do_triple___closed__7_value),((lean_object*)&l_Std_Do_triple___closed__10_value)}};
static const lean_object* l_Std_Do_triple___closed__11 = (const lean_object*)&l_Std_Do_triple___closed__11_value;
static const lean_string_object l_Std_Do_triple___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 2, .m_data = "⦄ "};
static const lean_object* l_Std_Do_triple___closed__12 = (const lean_object*)&l_Std_Do_triple___closed__12_value;
static const lean_ctor_object l_Std_Do_triple___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Do_triple___closed__12_value)}};
static const lean_object* l_Std_Do_triple___closed__13 = (const lean_object*)&l_Std_Do_triple___closed__13_value;
static const lean_ctor_object l_Std_Do_triple___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Do_triple___closed__5_value),((lean_object*)&l_Std_Do_triple___closed__11_value),((lean_object*)&l_Std_Do_triple___closed__13_value)}};
static const lean_object* l_Std_Do_triple___closed__14 = (const lean_object*)&l_Std_Do_triple___closed__14_value;
static const lean_ctor_object l_Std_Do_triple___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Std_Do_triple___closed__9_value),((lean_object*)(((size_t)(1022) << 1) | 1))}};
static const lean_object* l_Std_Do_triple___closed__15 = (const lean_object*)&l_Std_Do_triple___closed__15_value;
static const lean_ctor_object l_Std_Do_triple___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Do_triple___closed__5_value),((lean_object*)&l_Std_Do_triple___closed__14_value),((lean_object*)&l_Std_Do_triple___closed__15_value)}};
static const lean_object* l_Std_Do_triple___closed__16 = (const lean_object*)&l_Std_Do_triple___closed__16_value;
static const lean_string_object l_Std_Do_triple___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 2, .m_data = " ⦃"};
static const lean_object* l_Std_Do_triple___closed__17 = (const lean_object*)&l_Std_Do_triple___closed__17_value;
static const lean_ctor_object l_Std_Do_triple___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Do_triple___closed__17_value)}};
static const lean_object* l_Std_Do_triple___closed__18 = (const lean_object*)&l_Std_Do_triple___closed__18_value;
static const lean_ctor_object l_Std_Do_triple___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Do_triple___closed__5_value),((lean_object*)&l_Std_Do_triple___closed__16_value),((lean_object*)&l_Std_Do_triple___closed__18_value)}};
static const lean_object* l_Std_Do_triple___closed__19 = (const lean_object*)&l_Std_Do_triple___closed__19_value;
static const lean_ctor_object l_Std_Do_triple___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Do_triple___closed__5_value),((lean_object*)&l_Std_Do_triple___closed__19_value),((lean_object*)&l_Std_Do_triple___closed__10_value)}};
static const lean_object* l_Std_Do_triple___closed__20 = (const lean_object*)&l_Std_Do_triple___closed__20_value;
static const lean_string_object l_Std_Do_triple___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⦄"};
static const lean_object* l_Std_Do_triple___closed__21 = (const lean_object*)&l_Std_Do_triple___closed__21_value;
static const lean_ctor_object l_Std_Do_triple___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Do_triple___closed__21_value)}};
static const lean_object* l_Std_Do_triple___closed__22 = (const lean_object*)&l_Std_Do_triple___closed__22_value;
static const lean_ctor_object l_Std_Do_triple___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Do_triple___closed__5_value),((lean_object*)&l_Std_Do_triple___closed__20_value),((lean_object*)&l_Std_Do_triple___closed__22_value)}};
static const lean_object* l_Std_Do_triple___closed__23 = (const lean_object*)&l_Std_Do_triple___closed__23_value;
static const lean_ctor_object l_Std_Do_triple___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Do_triple___closed__3_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Std_Do_triple___closed__23_value)}};
static const lean_object* l_Std_Do_triple___closed__24 = (const lean_object*)&l_Std_Do_triple___closed__24_value;
LEAN_EXPORT const lean_object* l_Std_Do_triple = (const lean_object*)&l_Std_Do_triple___closed__24_value;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "termSpred(_)"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__0 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__0_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_triple___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__1_value_aux_0),((lean_object*)&l_Std_Do_triple___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__1_value_aux_1),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 240, 91, 148, 237, 191, 255, 193)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__1 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__1_value;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__2 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__2_value;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__3 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__3_value;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__4 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__4_value;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__5 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__5_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__6_value_aux_0),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__6_value_aux_1),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__6_value_aux_2),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__6 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__6_value;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "termIfThenElse"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__7 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__7_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(225, 209, 193, 165, 165, 31, 104, 198)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__8 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__8_value;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fun"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__9 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__9_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__10_value_aux_0),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__10_value_aux_1),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__10_value_aux_2),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__9_value),LEAN_SCALAR_PTR_LITERAL(249, 155, 133, 242, 71, 132, 191, 97)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__10 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__10_value;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "typeAscription"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__11 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__11_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__12_value_aux_0),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__12_value_aux_1),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__12_value_aux_2),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__11_value),LEAN_SCALAR_PTR_LITERAL(247, 209, 88, 141, 5, 195, 49, 74)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__12 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__12_value;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__13 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__13_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__14_value_aux_0),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__14_value_aux_1),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__14_value_aux_2),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__13_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__14 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__14_value;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__15 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__15_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__15_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__16 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__16_value;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_fakeMod"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__17 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__17_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__17_value),LEAN_SCALAR_PTR_LITERAL(168, 44, 241, 255, 153, 255, 67, 53)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__18 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__18_value;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__19 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__19_value;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__20 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__20_value;
static lean_once_cell_t l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__21;
static lean_once_cell_t l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__22;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "SPred"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__23 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__23_value;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Notation"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__24 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__24_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_triple___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__25_value_aux_0),((lean_object*)&l_Std_Do_triple___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__25_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__25_value_aux_1),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__23_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__25_value_aux_2),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__24_value),LEAN_SCALAR_PTR_LITERAL(66, 246, 126, 200, 193, 235, 124, 8)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__25 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__25_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__25_value)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__26 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__26_value;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "PrettyPrinter"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__27 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__27_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__28_value_aux_0),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__27_value),LEAN_SCALAR_PTR_LITERAL(120, 167, 117, 148, 131, 202, 42, 4)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__28 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__28_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__28_value)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__29 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__29_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__30_value_aux_0),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__30 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__30_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__30_value)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__31 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__31_value;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Macro"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__32 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__32_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__33_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__33_value_aux_0),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__32_value),LEAN_SCALAR_PTR_LITERAL(168, 205, 218, 0, 241, 122, 66, 251)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__33 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__33_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__33_value)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__34 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__34_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__35 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__35_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__35_value)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__36 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__36_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__36_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__37 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__37_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__34_value),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__37_value)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__38 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__38_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__31_value),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__38_value)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__39 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__39_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__29_value),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__39_value)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__40 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__40_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__26_value),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__40_value)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__41 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__41_value;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__42 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__42_value;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__43 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__43_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__43_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__44 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__44_value;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__45 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__45_value;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "basicFun"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__46 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__46_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__47_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__47_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__47_value_aux_0),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__47_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__47_value_aux_1),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__47_value_aux_2),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__46_value),LEAN_SCALAR_PTR_LITERAL(209, 134, 40, 160, 122, 195, 31, 223)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__47 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__47_value;
static lean_once_cell_t l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__48_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__48;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__49 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__49_value;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "if"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__50 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__50_value;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "then"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__51 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__51_value;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "else"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__52 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__52_value;
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Do_unexpandTriple___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Std_Do_unexpandTriple___closed__0 = (const lean_object*)&l_Std_Do_unexpandTriple___closed__0_value;
static const lean_ctor_object l_Std_Do_unexpandTriple___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Do_unexpandTriple___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_unexpandTriple___closed__1_value_aux_0),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Do_unexpandTriple___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_unexpandTriple___closed__1_value_aux_1),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Do_unexpandTriple___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_unexpandTriple___closed__1_value_aux_2),((lean_object*)&l_Std_Do_unexpandTriple___closed__0_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Std_Do_unexpandTriple___closed__1 = (const lean_object*)&l_Std_Do_unexpandTriple___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Do_unexpandTriple(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_unexpandTriple___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__21(void){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_104_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__20));
v___x_105_ = l_String_toRawSubstring_x27(v___x_104_);
return v___x_105_;
}
}
static lean_object* _init_l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__22(void){
_start:
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_106_ = lean_unsigned_to_nat(0u);
v___x_107_ = lean_box(0);
v___x_108_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__18));
v___x_109_ = l_Lean_addMacroScope(v___x_108_, v___x_107_, v___x_106_);
return v___x_109_;
}
}
static lean_object* _init_l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__48(void){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = l_Array_mkArray0(lean_box(0));
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0(lean_object* v_x_171_, lean_object* v___y_172_, lean_object* v___y_173_){
_start:
{
lean_object* v___x_174_; uint8_t v___x_175_; 
v___x_174_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__1));
lean_inc(v_x_171_);
v___x_175_ = l_Lean_Syntax_isOfKind(v_x_171_, v___x_174_);
if (v___x_175_ == 0)
{
lean_object* v___x_176_; uint8_t v___x_177_; 
v___x_176_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__6));
lean_inc(v_x_171_);
v___x_177_ = l_Lean_Syntax_isOfKind(v_x_171_, v___x_176_);
if (v___x_177_ == 0)
{
lean_object* v___x_178_; uint8_t v___x_179_; 
v___x_178_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__8));
lean_inc(v_x_171_);
v___x_179_ = l_Lean_Syntax_isOfKind(v_x_171_, v___x_178_);
if (v___x_179_ == 0)
{
lean_object* v___x_180_; lean_object* v___x_181_; uint8_t v___x_182_; 
v___x_180_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__9));
v___x_181_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__10));
lean_inc(v_x_171_);
v___x_182_ = l_Lean_Syntax_isOfKind(v_x_171_, v___x_181_);
if (v___x_182_ == 0)
{
lean_object* v___x_183_; uint8_t v___x_184_; 
v___x_183_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__12));
lean_inc(v_x_171_);
v___x_184_ = l_Lean_Syntax_isOfKind(v_x_171_, v___x_183_);
if (v___x_184_ == 0)
{
lean_object* v___x_185_; 
v___x_185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_185_, 0, v_x_171_);
lean_ctor_set(v___x_185_, 1, v___y_173_);
return v___x_185_;
}
else
{
lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; uint8_t v___x_189_; 
v___x_186_ = lean_unsigned_to_nat(0u);
v___x_187_ = l_Lean_Syntax_getArg(v_x_171_, v___x_186_);
v___x_188_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__14));
lean_inc(v___x_187_);
v___x_189_ = l_Lean_Syntax_isOfKind(v___x_187_, v___x_188_);
if (v___x_189_ == 0)
{
lean_object* v___x_190_; 
lean_dec(v___x_187_);
v___x_190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_190_, 0, v_x_171_);
lean_ctor_set(v___x_190_, 1, v___y_173_);
return v___x_190_;
}
else
{
lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; uint8_t v___x_194_; 
v___x_191_ = lean_unsigned_to_nat(1u);
v___x_192_ = l_Lean_Syntax_getArg(v___x_187_, v___x_191_);
lean_dec(v___x_187_);
v___x_193_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__16));
lean_inc(v___x_192_);
v___x_194_ = l_Lean_Syntax_isOfKind(v___x_192_, v___x_193_);
if (v___x_194_ == 0)
{
lean_object* v___x_195_; 
lean_dec(v___x_192_);
v___x_195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_195_, 0, v_x_171_);
lean_ctor_set(v___x_195_, 1, v___y_173_);
return v___x_195_;
}
else
{
lean_object* v___x_196_; lean_object* v___x_197_; uint8_t v___x_198_; 
v___x_196_ = l_Lean_Syntax_getArg(v___x_192_, v___x_186_);
lean_dec(v___x_192_);
v___x_197_ = lean_box(0);
v___x_198_ = l_Lean_Syntax_matchesIdent(v___x_196_, v___x_197_);
lean_dec(v___x_196_);
if (v___x_198_ == 0)
{
lean_object* v___x_199_; 
v___x_199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_199_, 0, v_x_171_);
lean_ctor_set(v___x_199_, 1, v___y_173_);
return v___x_199_;
}
else
{
lean_object* v___x_200_; lean_object* v___x_201_; uint8_t v___x_202_; 
v___x_200_ = lean_unsigned_to_nat(3u);
v___x_201_ = l_Lean_Syntax_getArg(v_x_171_, v___x_200_);
lean_inc(v___x_201_);
v___x_202_ = l_Lean_Syntax_matchesNull(v___x_201_, v___x_191_);
if (v___x_202_ == 0)
{
lean_object* v___x_203_; 
lean_dec(v___x_201_);
v___x_203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_203_, 0, v_x_171_);
lean_ctor_set(v___x_203_, 1, v___y_173_);
return v___x_203_;
}
else
{
lean_object* v_P_204_; lean_object* v___x_205_; 
v_P_204_ = l_Lean_Syntax_getArg(v_x_171_, v___x_191_);
lean_dec(v_x_171_);
v___x_205_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0(v_P_204_, v___y_172_, v___y_173_);
if (lean_obj_tag(v___x_205_) == 0)
{
lean_object* v_a_206_; lean_object* v_a_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_231_; 
v_a_206_ = lean_ctor_get(v___x_205_, 0);
v_a_207_ = lean_ctor_get(v___x_205_, 1);
v_isSharedCheck_231_ = !lean_is_exclusive(v___x_205_);
if (v_isSharedCheck_231_ == 0)
{
v___x_209_ = v___x_205_;
v_isShared_210_ = v_isSharedCheck_231_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_a_207_);
lean_inc(v_a_206_);
lean_dec(v___x_205_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_231_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_229_; 
v___x_211_ = l_Lean_Syntax_getArg(v___x_201_, v___x_186_);
lean_dec(v___x_201_);
v___x_212_ = l_Lean_SourceInfo_fromRef(v___y_172_, v___x_182_);
v___x_213_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__19));
lean_inc(v___x_212_);
v___x_214_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_214_, 0, v___x_212_);
lean_ctor_set(v___x_214_, 1, v___x_213_);
v___x_215_ = lean_obj_once(&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__21, &l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__21_once, _init_l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__21);
v___x_216_ = lean_obj_once(&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__22, &l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__22_once, _init_l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__22);
v___x_217_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__41));
lean_inc(v___x_212_);
v___x_218_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_218_, 0, v___x_212_);
lean_ctor_set(v___x_218_, 1, v___x_215_);
lean_ctor_set(v___x_218_, 2, v___x_216_);
lean_ctor_set(v___x_218_, 3, v___x_217_);
lean_inc(v___x_212_);
v___x_219_ = l_Lean_Syntax_node1(v___x_212_, v___x_193_, v___x_218_);
lean_inc(v___x_212_);
v___x_220_ = l_Lean_Syntax_node2(v___x_212_, v___x_188_, v___x_214_, v___x_219_);
v___x_221_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__42));
lean_inc(v___x_212_);
v___x_222_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_222_, 0, v___x_212_);
lean_ctor_set(v___x_222_, 1, v___x_221_);
v___x_223_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__44));
lean_inc(v___x_212_);
v___x_224_ = l_Lean_Syntax_node1(v___x_212_, v___x_223_, v___x_211_);
v___x_225_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__45));
lean_inc(v___x_212_);
v___x_226_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_226_, 0, v___x_212_);
lean_ctor_set(v___x_226_, 1, v___x_225_);
v___x_227_ = l_Lean_Syntax_node5(v___x_212_, v___x_183_, v___x_220_, v_a_206_, v___x_222_, v___x_224_, v___x_226_);
if (v_isShared_210_ == 0)
{
lean_ctor_set(v___x_209_, 0, v___x_227_);
v___x_229_ = v___x_209_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v___x_227_);
lean_ctor_set(v_reuseFailAlloc_230_, 1, v_a_207_);
v___x_229_ = v_reuseFailAlloc_230_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
return v___x_229_;
}
}
}
else
{
lean_dec(v___x_201_);
return v___x_205_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; uint8_t v___x_235_; 
v___x_232_ = lean_unsigned_to_nat(1u);
v___x_233_ = l_Lean_Syntax_getArg(v_x_171_, v___x_232_);
v___x_234_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__47));
lean_inc(v___x_233_);
v___x_235_ = l_Lean_Syntax_isOfKind(v___x_233_, v___x_234_);
if (v___x_235_ == 0)
{
lean_object* v___x_236_; 
lean_dec(v___x_233_);
v___x_236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_236_, 0, v_x_171_);
lean_ctor_set(v___x_236_, 1, v___y_173_);
return v___x_236_;
}
else
{
lean_object* v___x_237_; lean_object* v___x_238_; uint8_t v___x_239_; 
v___x_237_ = lean_unsigned_to_nat(0u);
v___x_238_ = l_Lean_Syntax_getArg(v___x_233_, v___x_232_);
v___x_239_ = l_Lean_Syntax_matchesNull(v___x_238_, v___x_237_);
if (v___x_239_ == 0)
{
lean_object* v___x_240_; 
lean_dec(v___x_233_);
v___x_240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_240_, 0, v_x_171_);
lean_ctor_set(v___x_240_, 1, v___y_173_);
return v___x_240_;
}
else
{
lean_object* v___x_241_; lean_object* v_b_242_; lean_object* v___x_243_; 
lean_dec(v_x_171_);
v___x_241_ = lean_unsigned_to_nat(3u);
v_b_242_ = l_Lean_Syntax_getArg(v___x_233_, v___x_241_);
v___x_243_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0(v_b_242_, v___y_172_, v___y_173_);
if (lean_obj_tag(v___x_243_) == 0)
{
lean_object* v_a_244_; lean_object* v_a_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_265_; 
v_a_244_ = lean_ctor_get(v___x_243_, 0);
v_a_245_ = lean_ctor_get(v___x_243_, 1);
v_isSharedCheck_265_ = !lean_is_exclusive(v___x_243_);
if (v_isSharedCheck_265_ == 0)
{
v___x_247_ = v___x_243_;
v_isShared_248_ = v_isSharedCheck_265_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_a_245_);
lean_inc(v_a_244_);
lean_dec(v___x_243_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_265_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v___x_249_; lean_object* v_xs_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_263_; 
v___x_249_ = l_Lean_Syntax_getArg(v___x_233_, v___x_237_);
lean_dec(v___x_233_);
v_xs_250_ = l_Lean_Syntax_getArgs(v___x_249_);
lean_dec(v___x_249_);
v___x_251_ = l_Lean_SourceInfo_fromRef(v___y_172_, v___x_179_);
lean_inc(v___x_251_);
v___x_252_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_252_, 0, v___x_251_);
lean_ctor_set(v___x_252_, 1, v___x_180_);
v___x_253_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__44));
v___x_254_ = lean_obj_once(&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__48, &l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__48_once, _init_l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__48);
v___x_255_ = l_Array_append___redArg(v___x_254_, v_xs_250_);
lean_dec_ref(v_xs_250_);
lean_inc(v___x_251_);
v___x_256_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_256_, 0, v___x_251_);
lean_ctor_set(v___x_256_, 1, v___x_253_);
lean_ctor_set(v___x_256_, 2, v___x_255_);
lean_inc(v___x_251_);
v___x_257_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_257_, 0, v___x_251_);
lean_ctor_set(v___x_257_, 1, v___x_253_);
lean_ctor_set(v___x_257_, 2, v___x_254_);
v___x_258_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__49));
lean_inc(v___x_251_);
v___x_259_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_259_, 0, v___x_251_);
lean_ctor_set(v___x_259_, 1, v___x_258_);
lean_inc(v___x_251_);
v___x_260_ = l_Lean_Syntax_node4(v___x_251_, v___x_234_, v___x_256_, v___x_257_, v___x_259_, v_a_244_);
v___x_261_ = l_Lean_Syntax_node2(v___x_251_, v___x_181_, v___x_252_, v___x_260_);
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 0, v___x_261_);
v___x_263_ = v___x_247_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v___x_261_);
lean_ctor_set(v_reuseFailAlloc_264_, 1, v_a_245_);
v___x_263_ = v_reuseFailAlloc_264_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
return v___x_263_;
}
}
}
else
{
lean_dec(v___x_233_);
return v___x_243_;
}
}
}
}
}
else
{
lean_object* v___x_266_; lean_object* v_t_267_; lean_object* v___x_268_; 
v___x_266_ = lean_unsigned_to_nat(3u);
v_t_267_ = l_Lean_Syntax_getArg(v_x_171_, v___x_266_);
v___x_268_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0(v_t_267_, v___y_172_, v___y_173_);
if (lean_obj_tag(v___x_268_) == 0)
{
lean_object* v_a_269_; lean_object* v_a_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_298_; 
v_a_269_ = lean_ctor_get(v___x_268_, 0);
v_a_270_ = lean_ctor_get(v___x_268_, 1);
v_isSharedCheck_298_ = !lean_is_exclusive(v___x_268_);
if (v_isSharedCheck_298_ == 0)
{
v___x_272_ = v___x_268_;
v_isShared_273_ = v_isSharedCheck_298_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_a_270_);
lean_inc(v_a_269_);
lean_dec(v___x_268_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_298_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v___x_274_; lean_object* v_e_275_; lean_object* v___x_276_; 
v___x_274_ = lean_unsigned_to_nat(5u);
v_e_275_ = l_Lean_Syntax_getArg(v_x_171_, v___x_274_);
v___x_276_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0(v_e_275_, v___y_172_, v_a_270_);
if (lean_obj_tag(v___x_276_) == 0)
{
lean_object* v_a_277_; lean_object* v_a_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_297_; 
v_a_277_ = lean_ctor_get(v___x_276_, 0);
v_a_278_ = lean_ctor_get(v___x_276_, 1);
v_isSharedCheck_297_ = !lean_is_exclusive(v___x_276_);
if (v_isSharedCheck_297_ == 0)
{
v___x_280_ = v___x_276_;
v_isShared_281_ = v_isSharedCheck_297_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_a_278_);
lean_inc(v_a_277_);
lean_dec(v___x_276_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_297_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_287_; 
v___x_282_ = lean_unsigned_to_nat(1u);
v___x_283_ = l_Lean_Syntax_getArg(v_x_171_, v___x_282_);
lean_dec(v_x_171_);
v___x_284_ = l_Lean_SourceInfo_fromRef(v___y_172_, v___x_177_);
v___x_285_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__50));
lean_inc(v___x_284_);
if (v_isShared_273_ == 0)
{
lean_ctor_set_tag(v___x_272_, 2);
lean_ctor_set(v___x_272_, 1, v___x_285_);
lean_ctor_set(v___x_272_, 0, v___x_284_);
v___x_287_ = v___x_272_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v___x_284_);
lean_ctor_set(v_reuseFailAlloc_296_, 1, v___x_285_);
v___x_287_ = v_reuseFailAlloc_296_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_294_; 
v___x_288_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__51));
lean_inc(v___x_284_);
v___x_289_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_289_, 0, v___x_284_);
lean_ctor_set(v___x_289_, 1, v___x_288_);
v___x_290_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__52));
lean_inc(v___x_284_);
v___x_291_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_291_, 0, v___x_284_);
lean_ctor_set(v___x_291_, 1, v___x_290_);
v___x_292_ = l_Lean_Syntax_node6(v___x_284_, v___x_178_, v___x_287_, v___x_283_, v___x_289_, v_a_269_, v___x_291_, v_a_277_);
if (v_isShared_281_ == 0)
{
lean_ctor_set(v___x_280_, 0, v___x_292_);
v___x_294_ = v___x_280_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v___x_292_);
lean_ctor_set(v_reuseFailAlloc_295_, 1, v_a_278_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
return v___x_294_;
}
}
}
}
else
{
lean_del_object(v___x_272_);
lean_dec(v_a_269_);
lean_dec(v_x_171_);
return v___x_276_;
}
}
}
else
{
lean_dec(v_x_171_);
return v___x_268_;
}
}
}
else
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; uint8_t v___x_302_; 
v___x_299_ = lean_unsigned_to_nat(0u);
v___x_300_ = l_Lean_Syntax_getArg(v_x_171_, v___x_299_);
v___x_301_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__14));
lean_inc(v___x_300_);
v___x_302_ = l_Lean_Syntax_isOfKind(v___x_300_, v___x_301_);
if (v___x_302_ == 0)
{
lean_object* v___x_303_; 
lean_dec(v___x_300_);
v___x_303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_303_, 0, v_x_171_);
lean_ctor_set(v___x_303_, 1, v___y_173_);
return v___x_303_;
}
else
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; uint8_t v___x_307_; 
v___x_304_ = lean_unsigned_to_nat(1u);
v___x_305_ = l_Lean_Syntax_getArg(v___x_300_, v___x_304_);
lean_dec(v___x_300_);
v___x_306_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__16));
lean_inc(v___x_305_);
v___x_307_ = l_Lean_Syntax_isOfKind(v___x_305_, v___x_306_);
if (v___x_307_ == 0)
{
lean_object* v___x_308_; 
lean_dec(v___x_305_);
v___x_308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_308_, 0, v_x_171_);
lean_ctor_set(v___x_308_, 1, v___y_173_);
return v___x_308_;
}
else
{
lean_object* v___x_309_; lean_object* v___x_310_; uint8_t v___x_311_; 
v___x_309_ = l_Lean_Syntax_getArg(v___x_305_, v___x_299_);
lean_dec(v___x_305_);
v___x_310_ = lean_box(0);
v___x_311_ = l_Lean_Syntax_matchesIdent(v___x_309_, v___x_310_);
lean_dec(v___x_309_);
if (v___x_311_ == 0)
{
lean_object* v___x_312_; 
v___x_312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_312_, 0, v_x_171_);
lean_ctor_set(v___x_312_, 1, v___y_173_);
return v___x_312_;
}
else
{
lean_object* v_P_313_; lean_object* v___x_314_; 
v_P_313_ = l_Lean_Syntax_getArg(v_x_171_, v___x_304_);
lean_dec(v_x_171_);
v___x_314_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0(v_P_313_, v___y_172_, v___y_173_);
if (lean_obj_tag(v___x_314_) == 0)
{
lean_object* v_a_315_; lean_object* v_a_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_335_; 
v_a_315_ = lean_ctor_get(v___x_314_, 0);
v_a_316_ = lean_ctor_get(v___x_314_, 1);
v_isSharedCheck_335_ = !lean_is_exclusive(v___x_314_);
if (v_isSharedCheck_335_ == 0)
{
v___x_318_ = v___x_314_;
v_isShared_319_ = v_isSharedCheck_335_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_a_316_);
lean_inc(v_a_315_);
lean_dec(v___x_314_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_335_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_333_; 
v___x_320_ = l_Lean_SourceInfo_fromRef(v___y_172_, v___x_175_);
v___x_321_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__19));
lean_inc(v___x_320_);
v___x_322_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_322_, 0, v___x_320_);
lean_ctor_set(v___x_322_, 1, v___x_321_);
v___x_323_ = lean_obj_once(&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__21, &l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__21_once, _init_l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__21);
v___x_324_ = lean_obj_once(&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__22, &l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__22_once, _init_l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__22);
v___x_325_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__41));
lean_inc(v___x_320_);
v___x_326_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_326_, 0, v___x_320_);
lean_ctor_set(v___x_326_, 1, v___x_323_);
lean_ctor_set(v___x_326_, 2, v___x_324_);
lean_ctor_set(v___x_326_, 3, v___x_325_);
lean_inc(v___x_320_);
v___x_327_ = l_Lean_Syntax_node1(v___x_320_, v___x_306_, v___x_326_);
lean_inc(v___x_320_);
v___x_328_ = l_Lean_Syntax_node2(v___x_320_, v___x_301_, v___x_322_, v___x_327_);
v___x_329_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__45));
lean_inc(v___x_320_);
v___x_330_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_330_, 0, v___x_320_);
lean_ctor_set(v___x_330_, 1, v___x_329_);
v___x_331_ = l_Lean_Syntax_node3(v___x_320_, v___x_176_, v___x_328_, v_a_315_, v___x_330_);
if (v_isShared_319_ == 0)
{
lean_ctor_set(v___x_318_, 0, v___x_331_);
v___x_333_ = v___x_318_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v___x_331_);
lean_ctor_set(v_reuseFailAlloc_334_, 1, v_a_316_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
return v___x_333_;
}
}
}
else
{
return v___x_314_;
}
}
}
}
}
}
else
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_336_ = lean_unsigned_to_nat(1u);
v___x_337_ = l_Lean_Syntax_getArg(v_x_171_, v___x_336_);
lean_dec(v_x_171_);
v___x_338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_338_, 0, v___x_337_);
lean_ctor_set(v___x_338_, 1, v___y_173_);
return v___x_338_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___boxed(lean_object* v_x_339_, lean_object* v___y_340_, lean_object* v___y_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0(v_x_339_, v___y_340_, v___y_341_);
lean_dec(v___y_340_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_unexpandTriple(lean_object* v_x_349_, lean_object* v_a_350_, lean_object* v_a_351_){
_start:
{
lean_object* v___x_352_; uint8_t v___x_353_; 
v___x_352_ = ((lean_object*)(l_Std_Do_unexpandTriple___closed__1));
lean_inc(v_x_349_);
v___x_353_ = l_Lean_Syntax_isOfKind(v_x_349_, v___x_352_);
if (v___x_353_ == 0)
{
lean_object* v___x_354_; lean_object* v___x_355_; 
lean_dec(v_x_349_);
v___x_354_ = lean_box(0);
v___x_355_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_355_, 0, v___x_354_);
lean_ctor_set(v___x_355_, 1, v_a_351_);
return v___x_355_;
}
else
{
lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; uint8_t v___x_359_; 
v___x_356_ = lean_unsigned_to_nat(1u);
v___x_357_ = l_Lean_Syntax_getArg(v_x_349_, v___x_356_);
lean_dec(v_x_349_);
v___x_358_ = lean_unsigned_to_nat(3u);
lean_inc(v___x_357_);
v___x_359_ = l_Lean_Syntax_matchesNull(v___x_357_, v___x_358_);
if (v___x_359_ == 0)
{
lean_object* v___x_360_; lean_object* v___x_361_; 
lean_dec(v___x_357_);
v___x_360_ = lean_box(0);
v___x_361_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_361_, 0, v___x_360_);
lean_ctor_set(v___x_361_, 1, v_a_351_);
return v___x_361_;
}
else
{
lean_object* v_P_362_; lean_object* v___x_363_; 
v_P_362_ = l_Lean_Syntax_getArg(v___x_357_, v___x_356_);
v___x_363_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0(v_P_362_, v_a_350_, v_a_351_);
if (lean_obj_tag(v___x_363_) == 0)
{
lean_object* v_a_364_; lean_object* v_a_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_384_; 
v_a_364_ = lean_ctor_get(v___x_363_, 0);
v_a_365_ = lean_ctor_get(v___x_363_, 1);
v_isSharedCheck_384_ = !lean_is_exclusive(v___x_363_);
if (v_isSharedCheck_384_ == 0)
{
v___x_367_ = v___x_363_;
v_isShared_368_ = v_isSharedCheck_384_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_a_365_);
lean_inc(v_a_364_);
lean_dec(v___x_363_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_384_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; uint8_t v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_382_; 
v___x_369_ = lean_unsigned_to_nat(0u);
v___x_370_ = l_Lean_Syntax_getArg(v___x_357_, v___x_369_);
v___x_371_ = lean_unsigned_to_nat(2u);
v___x_372_ = l_Lean_Syntax_getArg(v___x_357_, v___x_371_);
lean_dec(v___x_357_);
v___x_373_ = 0;
v___x_374_ = l_Lean_SourceInfo_fromRef(v_a_350_, v___x_373_);
v___x_375_ = ((lean_object*)(l_Std_Do_triple___closed__3));
v___x_376_ = ((lean_object*)(l_Std_Do_triple___closed__6));
lean_inc(v___x_374_);
v___x_377_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_377_, 0, v___x_374_);
lean_ctor_set(v___x_377_, 1, v___x_376_);
v___x_378_ = ((lean_object*)(l_Std_Do_triple___closed__21));
lean_inc(v___x_374_);
v___x_379_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_379_, 0, v___x_374_);
lean_ctor_set(v___x_379_, 1, v___x_378_);
lean_inc_ref(v___x_379_);
lean_inc_ref(v___x_377_);
v___x_380_ = l_Lean_Syntax_node7(v___x_374_, v___x_375_, v___x_377_, v_a_364_, v___x_379_, v___x_370_, v___x_377_, v___x_372_, v___x_379_);
if (v_isShared_368_ == 0)
{
lean_ctor_set(v___x_367_, 0, v___x_380_);
v___x_382_ = v___x_367_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v___x_380_);
lean_ctor_set(v_reuseFailAlloc_383_, 1, v_a_365_);
v___x_382_ = v_reuseFailAlloc_383_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
return v___x_382_;
}
}
}
else
{
lean_object* v_a_385_; lean_object* v_a_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_393_; 
lean_dec(v___x_357_);
v_a_385_ = lean_ctor_get(v___x_363_, 0);
v_a_386_ = lean_ctor_get(v___x_363_, 1);
v_isSharedCheck_393_ = !lean_is_exclusive(v___x_363_);
if (v_isSharedCheck_393_ == 0)
{
v___x_388_ = v___x_363_;
v_isShared_389_ = v_isSharedCheck_393_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_a_386_);
lean_inc(v_a_385_);
lean_dec(v___x_363_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_393_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v___x_391_; 
if (v_isShared_389_ == 0)
{
v___x_391_ = v___x_388_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v_a_385_);
lean_ctor_set(v_reuseFailAlloc_392_, 1, v_a_386_);
v___x_391_ = v_reuseFailAlloc_392_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
return v___x_391_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_unexpandTriple___boxed(lean_object* v_x_394_, lean_object* v_a_395_, lean_object* v_a_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Std_Do_unexpandTriple(v_x_394_, v_a_395_, v_a_396_);
lean_dec(v_a_395_);
return v_res_397_;
}
}
lean_object* runtime_initialize_Std_Do_WP(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Do_Triple_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Do_WP(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Do_Triple_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Do_WP(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Do_Triple_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Do_WP(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Do_Triple_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Do_Triple_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Do_Triple_Basic(builtin);
}
#ifdef __cplusplus
}
#endif

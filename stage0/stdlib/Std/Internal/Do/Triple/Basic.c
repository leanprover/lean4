// Lean compiler output
// Module: Std.Internal.Do.Triple.Basic
// Imports: public import Std.Internal.Do.WP public import Std.Internal.Do.ExceptPost
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
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesIdent(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__0 = (const lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__0_value;
static const lean_string_object l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__1 = (const lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__1_value;
static const lean_string_object l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__2 = (const lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__2_value;
static const lean_string_object l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__3 = (const lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__3_value;
static const lean_ctor_object l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__4_value_aux_0),((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__4_value_aux_1),((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__4_value_aux_2),((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__3_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__4 = (const lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__4_value;
static const lean_string_object l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "match"};
static const lean_object* l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__5 = (const lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__5_value;
static const lean_ctor_object l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__6_value_aux_0),((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__6_value_aux_1),((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__6_value_aux_2),((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__5_value),LEAN_SCALAR_PTR_LITERAL(9, 208, 235, 82, 91, 230, 203, 159)}};
static const lean_object* l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__6 = (const lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__6_value;
static const lean_string_object l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "termIfThenElse"};
static const lean_object* l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__7 = (const lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__7_value;
static const lean_ctor_object l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__7_value),LEAN_SCALAR_PTR_LITERAL(225, 209, 193, 165, 165, 31, 104, 198)}};
static const lean_object* l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__8 = (const lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__8_value;
static const lean_string_object l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "termDepIfThenElse"};
static const lean_object* l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__9 = (const lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__9_value;
static const lean_ctor_object l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__9_value),LEAN_SCALAR_PTR_LITERAL(191, 94, 17, 11, 145, 108, 236, 173)}};
static const lean_object* l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__10 = (const lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__10_value;
static const lean_string_object l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "do"};
static const lean_object* l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__11 = (const lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__11_value;
static const lean_ctor_object l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__12_value_aux_0),((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__12_value_aux_1),((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__12_value_aux_2),((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__11_value),LEAN_SCALAR_PTR_LITERAL(181, 206, 135, 90, 45, 65, 187, 80)}};
static const lean_object* l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__12 = (const lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__12_value;
LEAN_EXPORT uint8_t l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___boxed(lean_object*);
static const lean_string_object l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "typeAscription"};
static const lean_object* l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__0 = (const lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__0_value;
static const lean_ctor_object l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__1_value_aux_0),((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__1_value_aux_1),((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__1_value_aux_2),((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__0_value),LEAN_SCALAR_PTR_LITERAL(247, 209, 88, 141, 5, 195, 49, 74)}};
static const lean_object* l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__1 = (const lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__1_value;
static const lean_string_object l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__2 = (const lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__2_value;
static const lean_ctor_object l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__3_value_aux_0),((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__3_value_aux_1),((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__3_value_aux_2),((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__2_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__3 = (const lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__3_value;
static const lean_string_object l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__4 = (const lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__4_value;
static const lean_string_object l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__5 = (const lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__5_value;
static const lean_ctor_object l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__5_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__6 = (const lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__6_value;
static const lean_string_object l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__7 = (const lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__7_value;
static lean_once_cell_t l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__8;
static const lean_string_object l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__9 = (const lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__9_value;
static const lean_string_object l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Internal"};
static const lean_object* l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__10 = (const lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__10_value;
static const lean_string_object l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__11 = (const lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__11_value;
static const lean_ctor_object l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__9_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__12_value_aux_0),((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__10_value),LEAN_SCALAR_PTR_LITERAL(225, 148, 172, 135, 227, 248, 47, 24)}};
static const lean_ctor_object l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__12_value_aux_1),((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__11_value),LEAN_SCALAR_PTR_LITERAL(165, 204, 33, 109, 120, 201, 43, 17)}};
static const lean_object* l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__12 = (const lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__12_value;
static const lean_ctor_object l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__12_value)}};
static const lean_object* l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__13 = (const lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__13_value;
static const lean_ctor_object l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_object* l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__14 = (const lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__14_value;
static const lean_ctor_object l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__14_value)}};
static const lean_object* l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__15 = (const lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__15_value;
static const lean_string_object l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Order"};
static const lean_object* l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__16 = (const lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__16_value;
static const lean_ctor_object l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__17_value_aux_0),((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__16_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_object* l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__17 = (const lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__17_value;
static const lean_ctor_object l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__17_value)}};
static const lean_object* l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__18 = (const lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__18_value;
static const lean_ctor_object l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__18_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__19 = (const lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__19_value;
static const lean_ctor_object l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__15_value),((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__19_value)}};
static const lean_object* l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__20 = (const lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__20_value;
static const lean_ctor_object l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__13_value),((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__20_value)}};
static const lean_object* l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__21 = (const lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__21_value;
static const lean_string_object l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__22 = (const lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__22_value;
static const lean_string_object l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__23 = (const lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__23_value;
static const lean_ctor_object l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__23_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__24 = (const lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__24_value;
static const lean_string_object l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__25 = (const lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__25_value;
static const lean_ctor_object l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__26_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__26_value_aux_0),((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__26_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__26_value_aux_1),((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__26_value_aux_2),((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__25_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__26 = (const lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__26_value;
static const lean_string_object l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__27 = (const lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__27_value;
static const lean_ctor_object l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__28_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__28_value_aux_0),((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__28_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__28_value_aux_1),((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__28_value_aux_2),((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__27_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__28 = (const lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__28_value;
static const lean_string_object l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__29 = (const lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__29_value;
static const lean_string_object l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "arrow"};
static const lean_object* l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__30 = (const lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__30_value;
static const lean_ctor_object l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__31_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__31_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__31_value_aux_0),((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__31_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__31_value_aux_1),((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__31_value_aux_2),((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__30_value),LEAN_SCALAR_PTR_LITERAL(182, 146, 143, 73, 122, 115, 5, 207)}};
static const lean_object* l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__31 = (const lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__31_value;
static const lean_string_object l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "→"};
static const lean_object* l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__32 = (const lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__32_value;
static const lean_string_object l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__33 = (const lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__33_value;
LEAN_EXPORT lean_object* l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_Do_tripleNotation___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "tripleNotation"};
static const lean_object* l_Std_Internal_Do_tripleNotation___closed__0 = (const lean_object*)&l_Std_Internal_Do_tripleNotation___closed__0_value;
static const lean_ctor_object l_Std_Internal_Do_tripleNotation___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__9_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Internal_Do_tripleNotation___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__1_value_aux_0),((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__10_value),LEAN_SCALAR_PTR_LITERAL(225, 148, 172, 135, 227, 248, 47, 24)}};
static const lean_ctor_object l_Std_Internal_Do_tripleNotation___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__1_value_aux_1),((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__11_value),LEAN_SCALAR_PTR_LITERAL(165, 204, 33, 109, 120, 201, 43, 17)}};
static const lean_ctor_object l_Std_Internal_Do_tripleNotation___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__1_value_aux_2),((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__0_value),LEAN_SCALAR_PTR_LITERAL(215, 27, 222, 72, 43, 221, 122, 229)}};
static const lean_object* l_Std_Internal_Do_tripleNotation___closed__1 = (const lean_object*)&l_Std_Internal_Do_tripleNotation___closed__1_value;
static const lean_string_object l_Std_Internal_Do_tripleNotation___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Std_Internal_Do_tripleNotation___closed__2 = (const lean_object*)&l_Std_Internal_Do_tripleNotation___closed__2_value;
static const lean_ctor_object l_Std_Internal_Do_tripleNotation___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__2_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Std_Internal_Do_tripleNotation___closed__3 = (const lean_object*)&l_Std_Internal_Do_tripleNotation___closed__3_value;
static const lean_string_object l_Std_Internal_Do_tripleNotation___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 2, .m_data = "⦃ "};
static const lean_object* l_Std_Internal_Do_tripleNotation___closed__4 = (const lean_object*)&l_Std_Internal_Do_tripleNotation___closed__4_value;
static const lean_ctor_object l_Std_Internal_Do_tripleNotation___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__4_value)}};
static const lean_object* l_Std_Internal_Do_tripleNotation___closed__5 = (const lean_object*)&l_Std_Internal_Do_tripleNotation___closed__5_value;
static const lean_string_object l_Std_Internal_Do_tripleNotation___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Std_Internal_Do_tripleNotation___closed__6 = (const lean_object*)&l_Std_Internal_Do_tripleNotation___closed__6_value;
static const lean_ctor_object l_Std_Internal_Do_tripleNotation___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__6_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Std_Internal_Do_tripleNotation___closed__7 = (const lean_object*)&l_Std_Internal_Do_tripleNotation___closed__7_value;
static const lean_ctor_object l_Std_Internal_Do_tripleNotation___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__7_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Internal_Do_tripleNotation___closed__8 = (const lean_object*)&l_Std_Internal_Do_tripleNotation___closed__8_value;
static const lean_ctor_object l_Std_Internal_Do_tripleNotation___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__3_value),((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__5_value),((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__8_value)}};
static const lean_object* l_Std_Internal_Do_tripleNotation___closed__9 = (const lean_object*)&l_Std_Internal_Do_tripleNotation___closed__9_value;
static const lean_string_object l_Std_Internal_Do_tripleNotation___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 3, .m_data = " ⦄ "};
static const lean_object* l_Std_Internal_Do_tripleNotation___closed__10 = (const lean_object*)&l_Std_Internal_Do_tripleNotation___closed__10_value;
static const lean_ctor_object l_Std_Internal_Do_tripleNotation___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__10_value)}};
static const lean_object* l_Std_Internal_Do_tripleNotation___closed__11 = (const lean_object*)&l_Std_Internal_Do_tripleNotation___closed__11_value;
static const lean_ctor_object l_Std_Internal_Do_tripleNotation___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__3_value),((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__9_value),((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__11_value)}};
static const lean_object* l_Std_Internal_Do_tripleNotation___closed__12 = (const lean_object*)&l_Std_Internal_Do_tripleNotation___closed__12_value;
static const lean_string_object l_Std_Internal_Do_tripleNotation___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "optional"};
static const lean_object* l_Std_Internal_Do_tripleNotation___closed__13 = (const lean_object*)&l_Std_Internal_Do_tripleNotation___closed__13_value;
static const lean_ctor_object l_Std_Internal_Do_tripleNotation___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__13_value),LEAN_SCALAR_PTR_LITERAL(233, 141, 154, 50, 143, 135, 42, 252)}};
static const lean_object* l_Std_Internal_Do_tripleNotation___closed__14 = (const lean_object*)&l_Std_Internal_Do_tripleNotation___closed__14_value;
static const lean_string_object l_Std_Internal_Do_tripleNotation___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "atomic"};
static const lean_object* l_Std_Internal_Do_tripleNotation___closed__15 = (const lean_object*)&l_Std_Internal_Do_tripleNotation___closed__15_value;
static const lean_ctor_object l_Std_Internal_Do_tripleNotation___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__15_value),LEAN_SCALAR_PTR_LITERAL(56, 145, 113, 208, 127, 167, 216, 55)}};
static const lean_object* l_Std_Internal_Do_tripleNotation___closed__16 = (const lean_object*)&l_Std_Internal_Do_tripleNotation___closed__16_value;
static const lean_ctor_object l_Std_Internal_Do_tripleNotation___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__4_value)}};
static const lean_object* l_Std_Internal_Do_tripleNotation___closed__17 = (const lean_object*)&l_Std_Internal_Do_tripleNotation___closed__17_value;
static const lean_string_object l_Std_Internal_Do_tripleNotation___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Std_Internal_Do_tripleNotation___closed__18 = (const lean_object*)&l_Std_Internal_Do_tripleNotation___closed__18_value;
static const lean_ctor_object l_Std_Internal_Do_tripleNotation___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__18_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Std_Internal_Do_tripleNotation___closed__19 = (const lean_object*)&l_Std_Internal_Do_tripleNotation___closed__19_value;
static const lean_ctor_object l_Std_Internal_Do_tripleNotation___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__19_value)}};
static const lean_object* l_Std_Internal_Do_tripleNotation___closed__20 = (const lean_object*)&l_Std_Internal_Do_tripleNotation___closed__20_value;
static const lean_ctor_object l_Std_Internal_Do_tripleNotation___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__3_value),((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__17_value),((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__20_value)}};
static const lean_object* l_Std_Internal_Do_tripleNotation___closed__21 = (const lean_object*)&l_Std_Internal_Do_tripleNotation___closed__21_value;
static const lean_string_object l_Std_Internal_Do_tripleNotation___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Std_Internal_Do_tripleNotation___closed__22 = (const lean_object*)&l_Std_Internal_Do_tripleNotation___closed__22_value;
static const lean_ctor_object l_Std_Internal_Do_tripleNotation___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__22_value)}};
static const lean_object* l_Std_Internal_Do_tripleNotation___closed__23 = (const lean_object*)&l_Std_Internal_Do_tripleNotation___closed__23_value;
static const lean_ctor_object l_Std_Internal_Do_tripleNotation___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__3_value),((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__21_value),((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__23_value)}};
static const lean_object* l_Std_Internal_Do_tripleNotation___closed__24 = (const lean_object*)&l_Std_Internal_Do_tripleNotation___closed__24_value;
static const lean_ctor_object l_Std_Internal_Do_tripleNotation___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__16_value),((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__24_value)}};
static const lean_object* l_Std_Internal_Do_tripleNotation___closed__25 = (const lean_object*)&l_Std_Internal_Do_tripleNotation___closed__25_value;
static const lean_ctor_object l_Std_Internal_Do_tripleNotation___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__3_value),((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__25_value),((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__8_value)}};
static const lean_object* l_Std_Internal_Do_tripleNotation___closed__26 = (const lean_object*)&l_Std_Internal_Do_tripleNotation___closed__26_value;
static const lean_ctor_object l_Std_Internal_Do_tripleNotation___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__33_value)}};
static const lean_object* l_Std_Internal_Do_tripleNotation___closed__27 = (const lean_object*)&l_Std_Internal_Do_tripleNotation___closed__27_value;
static const lean_ctor_object l_Std_Internal_Do_tripleNotation___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__3_value),((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__26_value),((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__27_value)}};
static const lean_object* l_Std_Internal_Do_tripleNotation___closed__28 = (const lean_object*)&l_Std_Internal_Do_tripleNotation___closed__28_value;
static const lean_ctor_object l_Std_Internal_Do_tripleNotation___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__14_value),((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__28_value)}};
static const lean_object* l_Std_Internal_Do_tripleNotation___closed__29 = (const lean_object*)&l_Std_Internal_Do_tripleNotation___closed__29_value;
static const lean_ctor_object l_Std_Internal_Do_tripleNotation___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__3_value),((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__12_value),((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__29_value)}};
static const lean_object* l_Std_Internal_Do_tripleNotation___closed__30 = (const lean_object*)&l_Std_Internal_Do_tripleNotation___closed__30_value;
static const lean_ctor_object l_Std_Internal_Do_tripleNotation___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__3_value),((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__30_value),((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__8_value)}};
static const lean_object* l_Std_Internal_Do_tripleNotation___closed__31 = (const lean_object*)&l_Std_Internal_Do_tripleNotation___closed__31_value;
static const lean_string_object l_Std_Internal_Do_tripleNotation___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 3, .m_data = " ⦃ "};
static const lean_object* l_Std_Internal_Do_tripleNotation___closed__32 = (const lean_object*)&l_Std_Internal_Do_tripleNotation___closed__32_value;
static const lean_ctor_object l_Std_Internal_Do_tripleNotation___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__32_value)}};
static const lean_object* l_Std_Internal_Do_tripleNotation___closed__33 = (const lean_object*)&l_Std_Internal_Do_tripleNotation___closed__33_value;
static const lean_ctor_object l_Std_Internal_Do_tripleNotation___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__3_value),((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__31_value),((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__33_value)}};
static const lean_object* l_Std_Internal_Do_tripleNotation___closed__34 = (const lean_object*)&l_Std_Internal_Do_tripleNotation___closed__34_value;
static const lean_ctor_object l_Std_Internal_Do_tripleNotation___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__3_value),((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__34_value),((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__8_value)}};
static const lean_object* l_Std_Internal_Do_tripleNotation___closed__35 = (const lean_object*)&l_Std_Internal_Do_tripleNotation___closed__35_value;
static const lean_string_object l_Std_Internal_Do_tripleNotation___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 2, .m_data = " ⦄"};
static const lean_object* l_Std_Internal_Do_tripleNotation___closed__36 = (const lean_object*)&l_Std_Internal_Do_tripleNotation___closed__36_value;
static const lean_ctor_object l_Std_Internal_Do_tripleNotation___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__36_value)}};
static const lean_object* l_Std_Internal_Do_tripleNotation___closed__37 = (const lean_object*)&l_Std_Internal_Do_tripleNotation___closed__37_value;
static const lean_ctor_object l_Std_Internal_Do_tripleNotation___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__3_value),((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__35_value),((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__37_value)}};
static const lean_object* l_Std_Internal_Do_tripleNotation___closed__38 = (const lean_object*)&l_Std_Internal_Do_tripleNotation___closed__38_value;
static const lean_ctor_object l_Std_Internal_Do_tripleNotation___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__1_value),((lean_object*)(((size_t)(60) << 1) | 1)),((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__38_value)}};
static const lean_object* l_Std_Internal_Do_tripleNotation___closed__39 = (const lean_object*)&l_Std_Internal_Do_tripleNotation___closed__39_value;
LEAN_EXPORT const lean_object* l_Std_Internal_Do_tripleNotation = (const lean_object*)&l_Std_Internal_Do_tripleNotation___closed__39_value;
static const lean_string_object l_Std_Internal_Do_tripleBinderNotation___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "tripleBinderNotation"};
static const lean_object* l_Std_Internal_Do_tripleBinderNotation___closed__0 = (const lean_object*)&l_Std_Internal_Do_tripleBinderNotation___closed__0_value;
static const lean_ctor_object l_Std_Internal_Do_tripleBinderNotation___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__9_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Internal_Do_tripleBinderNotation___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do_tripleBinderNotation___closed__1_value_aux_0),((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__10_value),LEAN_SCALAR_PTR_LITERAL(225, 148, 172, 135, 227, 248, 47, 24)}};
static const lean_ctor_object l_Std_Internal_Do_tripleBinderNotation___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do_tripleBinderNotation___closed__1_value_aux_1),((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__11_value),LEAN_SCALAR_PTR_LITERAL(165, 204, 33, 109, 120, 201, 43, 17)}};
static const lean_ctor_object l_Std_Internal_Do_tripleBinderNotation___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do_tripleBinderNotation___closed__1_value_aux_2),((lean_object*)&l_Std_Internal_Do_tripleBinderNotation___closed__0_value),LEAN_SCALAR_PTR_LITERAL(74, 87, 102, 173, 151, 204, 230, 194)}};
static const lean_object* l_Std_Internal_Do_tripleBinderNotation___closed__1 = (const lean_object*)&l_Std_Internal_Do_tripleBinderNotation___closed__1_value;
static const lean_ctor_object l_Std_Internal_Do_tripleBinderNotation___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__3_value),((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__34_value),((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__20_value)}};
static const lean_object* l_Std_Internal_Do_tripleBinderNotation___closed__2 = (const lean_object*)&l_Std_Internal_Do_tripleBinderNotation___closed__2_value;
static const lean_string_object l_Std_Internal_Do_tripleBinderNotation___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_Std_Internal_Do_tripleBinderNotation___closed__3 = (const lean_object*)&l_Std_Internal_Do_tripleBinderNotation___closed__3_value;
static const lean_ctor_object l_Std_Internal_Do_tripleBinderNotation___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Internal_Do_tripleBinderNotation___closed__3_value)}};
static const lean_object* l_Std_Internal_Do_tripleBinderNotation___closed__4 = (const lean_object*)&l_Std_Internal_Do_tripleBinderNotation___closed__4_value;
static const lean_ctor_object l_Std_Internal_Do_tripleBinderNotation___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__3_value),((lean_object*)&l_Std_Internal_Do_tripleBinderNotation___closed__2_value),((lean_object*)&l_Std_Internal_Do_tripleBinderNotation___closed__4_value)}};
static const lean_object* l_Std_Internal_Do_tripleBinderNotation___closed__5 = (const lean_object*)&l_Std_Internal_Do_tripleBinderNotation___closed__5_value;
static const lean_ctor_object l_Std_Internal_Do_tripleBinderNotation___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__3_value),((lean_object*)&l_Std_Internal_Do_tripleBinderNotation___closed__5_value),((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__8_value)}};
static const lean_object* l_Std_Internal_Do_tripleBinderNotation___closed__6 = (const lean_object*)&l_Std_Internal_Do_tripleBinderNotation___closed__6_value;
static const lean_ctor_object l_Std_Internal_Do_tripleBinderNotation___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__3_value),((lean_object*)&l_Std_Internal_Do_tripleBinderNotation___closed__6_value),((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__37_value)}};
static const lean_object* l_Std_Internal_Do_tripleBinderNotation___closed__7 = (const lean_object*)&l_Std_Internal_Do_tripleBinderNotation___closed__7_value;
static const lean_ctor_object l_Std_Internal_Do_tripleBinderNotation___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_Do_tripleBinderNotation___closed__1_value),((lean_object*)(((size_t)(60) << 1) | 1)),((lean_object*)&l_Std_Internal_Do_tripleBinderNotation___closed__7_value)}};
static const lean_object* l_Std_Internal_Do_tripleBinderNotation___closed__8 = (const lean_object*)&l_Std_Internal_Do_tripleBinderNotation___closed__8_value;
LEAN_EXPORT const lean_object* l_Std_Internal_Do_tripleBinderNotation = (const lean_object*)&l_Std_Internal_Do_tripleBinderNotation___closed__8_value;
static const lean_string_object l_Std_Internal_Do_tripleEPost___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "tripleEPost"};
static const lean_object* l_Std_Internal_Do_tripleEPost___closed__0 = (const lean_object*)&l_Std_Internal_Do_tripleEPost___closed__0_value;
static const lean_ctor_object l_Std_Internal_Do_tripleEPost___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__9_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Internal_Do_tripleEPost___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do_tripleEPost___closed__1_value_aux_0),((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__10_value),LEAN_SCALAR_PTR_LITERAL(225, 148, 172, 135, 227, 248, 47, 24)}};
static const lean_ctor_object l_Std_Internal_Do_tripleEPost___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do_tripleEPost___closed__1_value_aux_1),((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__11_value),LEAN_SCALAR_PTR_LITERAL(165, 204, 33, 109, 120, 201, 43, 17)}};
static const lean_ctor_object l_Std_Internal_Do_tripleEPost___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do_tripleEPost___closed__1_value_aux_2),((lean_object*)&l_Std_Internal_Do_tripleEPost___closed__0_value),LEAN_SCALAR_PTR_LITERAL(79, 228, 187, 179, 135, 251, 133, 128)}};
static const lean_object* l_Std_Internal_Do_tripleEPost___closed__1 = (const lean_object*)&l_Std_Internal_Do_tripleEPost___closed__1_value;
static const lean_string_object l_Std_Internal_Do_tripleEPost___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "; "};
static const lean_object* l_Std_Internal_Do_tripleEPost___closed__2 = (const lean_object*)&l_Std_Internal_Do_tripleEPost___closed__2_value;
static const lean_ctor_object l_Std_Internal_Do_tripleEPost___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Internal_Do_tripleEPost___closed__2_value)}};
static const lean_object* l_Std_Internal_Do_tripleEPost___closed__3 = (const lean_object*)&l_Std_Internal_Do_tripleEPost___closed__3_value;
static const lean_ctor_object l_Std_Internal_Do_tripleEPost___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__3_value),((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__35_value),((lean_object*)&l_Std_Internal_Do_tripleEPost___closed__3_value)}};
static const lean_object* l_Std_Internal_Do_tripleEPost___closed__4 = (const lean_object*)&l_Std_Internal_Do_tripleEPost___closed__4_value;
static const lean_ctor_object l_Std_Internal_Do_tripleEPost___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__3_value),((lean_object*)&l_Std_Internal_Do_tripleEPost___closed__4_value),((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__8_value)}};
static const lean_object* l_Std_Internal_Do_tripleEPost___closed__5 = (const lean_object*)&l_Std_Internal_Do_tripleEPost___closed__5_value;
static const lean_ctor_object l_Std_Internal_Do_tripleEPost___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__3_value),((lean_object*)&l_Std_Internal_Do_tripleEPost___closed__5_value),((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__37_value)}};
static const lean_object* l_Std_Internal_Do_tripleEPost___closed__6 = (const lean_object*)&l_Std_Internal_Do_tripleEPost___closed__6_value;
static const lean_ctor_object l_Std_Internal_Do_tripleEPost___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_Do_tripleEPost___closed__1_value),((lean_object*)(((size_t)(60) << 1) | 1)),((lean_object*)&l_Std_Internal_Do_tripleEPost___closed__6_value)}};
static const lean_object* l_Std_Internal_Do_tripleEPost___closed__7 = (const lean_object*)&l_Std_Internal_Do_tripleEPost___closed__7_value;
LEAN_EXPORT const lean_object* l_Std_Internal_Do_tripleEPost = (const lean_object*)&l_Std_Internal_Do_tripleEPost___closed__7_value;
static const lean_string_object l_Std_Internal_Do_tripleBinderEPost___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "tripleBinderEPost"};
static const lean_object* l_Std_Internal_Do_tripleBinderEPost___closed__0 = (const lean_object*)&l_Std_Internal_Do_tripleBinderEPost___closed__0_value;
static const lean_ctor_object l_Std_Internal_Do_tripleBinderEPost___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__9_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Internal_Do_tripleBinderEPost___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do_tripleBinderEPost___closed__1_value_aux_0),((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__10_value),LEAN_SCALAR_PTR_LITERAL(225, 148, 172, 135, 227, 248, 47, 24)}};
static const lean_ctor_object l_Std_Internal_Do_tripleBinderEPost___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do_tripleBinderEPost___closed__1_value_aux_1),((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__11_value),LEAN_SCALAR_PTR_LITERAL(165, 204, 33, 109, 120, 201, 43, 17)}};
static const lean_ctor_object l_Std_Internal_Do_tripleBinderEPost___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do_tripleBinderEPost___closed__1_value_aux_2),((lean_object*)&l_Std_Internal_Do_tripleBinderEPost___closed__0_value),LEAN_SCALAR_PTR_LITERAL(246, 209, 155, 224, 117, 176, 249, 217)}};
static const lean_object* l_Std_Internal_Do_tripleBinderEPost___closed__1 = (const lean_object*)&l_Std_Internal_Do_tripleBinderEPost___closed__1_value;
static const lean_ctor_object l_Std_Internal_Do_tripleBinderEPost___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__3_value),((lean_object*)&l_Std_Internal_Do_tripleBinderNotation___closed__6_value),((lean_object*)&l_Std_Internal_Do_tripleEPost___closed__3_value)}};
static const lean_object* l_Std_Internal_Do_tripleBinderEPost___closed__2 = (const lean_object*)&l_Std_Internal_Do_tripleBinderEPost___closed__2_value;
static const lean_ctor_object l_Std_Internal_Do_tripleBinderEPost___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__3_value),((lean_object*)&l_Std_Internal_Do_tripleBinderEPost___closed__2_value),((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__8_value)}};
static const lean_object* l_Std_Internal_Do_tripleBinderEPost___closed__3 = (const lean_object*)&l_Std_Internal_Do_tripleBinderEPost___closed__3_value;
static const lean_ctor_object l_Std_Internal_Do_tripleBinderEPost___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__3_value),((lean_object*)&l_Std_Internal_Do_tripleBinderEPost___closed__3_value),((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__37_value)}};
static const lean_object* l_Std_Internal_Do_tripleBinderEPost___closed__4 = (const lean_object*)&l_Std_Internal_Do_tripleBinderEPost___closed__4_value;
static const lean_ctor_object l_Std_Internal_Do_tripleBinderEPost___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_Do_tripleBinderEPost___closed__1_value),((lean_object*)(((size_t)(60) << 1) | 1)),((lean_object*)&l_Std_Internal_Do_tripleBinderEPost___closed__4_value)}};
static const lean_object* l_Std_Internal_Do_tripleBinderEPost___closed__5 = (const lean_object*)&l_Std_Internal_Do_tripleBinderEPost___closed__5_value;
LEAN_EXPORT const lean_object* l_Std_Internal_Do_tripleBinderEPost = (const lean_object*)&l_Std_Internal_Do_tripleBinderEPost___closed__5_value;
static const lean_string_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Triple"};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__0 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__0_value;
static lean_once_cell_t l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__1;
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 148, 225, 137, 79, 125, 168, 172)}};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__2 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__2_value;
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__9_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__3_value_aux_0),((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__10_value),LEAN_SCALAR_PTR_LITERAL(225, 148, 172, 135, 227, 248, 47, 24)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__3_value_aux_1),((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__11_value),LEAN_SCALAR_PTR_LITERAL(165, 204, 33, 109, 120, 201, 43, 17)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__3_value_aux_2),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(190, 57, 218, 157, 42, 52, 8, 129)}};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__3 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__3_value;
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__4 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__4_value;
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__3_value)}};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__5 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__5_value;
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__6 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__6_value;
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__4_value),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__6_value)}};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__7 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__7_value;
static const lean_string_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Lean.Order.bot"};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__8 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__8_value;
static lean_once_cell_t l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__9;
static const lean_string_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "bot"};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__10 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__10_value;
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__11_value_aux_0),((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__16_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__11_value_aux_1),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(89, 51, 159, 172, 220, 225, 54, 137)}};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__11 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__11_value;
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__11_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__12 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__12_value;
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__12_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__13 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__13_value;
static const lean_string_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "m"};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__14 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__14_value;
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(165, 239, 73, 172, 230, 126, 139, 134)}};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__15 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__15_value;
LEAN_EXPORT lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__18_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__0 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__0_value;
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__13_value),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__0_value)}};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__1 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__1_value;
static const lean_string_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fun"};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__2 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__2_value;
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__3_value_aux_0),((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__3_value_aux_1),((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__3_value_aux_2),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(249, 155, 133, 242, 71, 132, 191, 97)}};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__3 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__3_value;
static const lean_string_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "basicFun"};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__4 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__4_value;
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__5_value_aux_0),((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__5_value_aux_1),((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__5_value_aux_2),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(209, 134, 40, 160, 122, 195, 31, 223)}};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__5 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__5_value;
static lean_once_cell_t l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__6;
static const lean_string_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__7 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__7_value;
LEAN_EXPORT lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleEPost__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleEPost__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderEPost__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderEPost__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_Do_unexpandTriple___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 5, .m_data = "term⊥"};
static const lean_object* l_Std_Internal_Do_unexpandTriple___closed__0 = (const lean_object*)&l_Std_Internal_Do_unexpandTriple___closed__0_value;
static const lean_ctor_object l_Std_Internal_Do_unexpandTriple___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Internal_Do_unexpandTriple___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do_unexpandTriple___closed__1_value_aux_0),((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__16_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Std_Internal_Do_unexpandTriple___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do_unexpandTriple___closed__1_value_aux_1),((lean_object*)&l_Std_Internal_Do_unexpandTriple___closed__0_value),LEAN_SCALAR_PTR_LITERAL(232, 78, 68, 112, 65, 121, 100, 195)}};
static const lean_object* l_Std_Internal_Do_unexpandTriple___closed__1 = (const lean_object*)&l_Std_Internal_Do_unexpandTriple___closed__1_value;
static const lean_string_object l_Std_Internal_Do_unexpandTriple___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⦃"};
static const lean_object* l_Std_Internal_Do_unexpandTriple___closed__2 = (const lean_object*)&l_Std_Internal_Do_unexpandTriple___closed__2_value;
static const lean_string_object l_Std_Internal_Do_unexpandTriple___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⦄"};
static const lean_object* l_Std_Internal_Do_unexpandTriple___closed__3 = (const lean_object*)&l_Std_Internal_Do_unexpandTriple___closed__3_value;
static const lean_string_object l_Std_Internal_Do_unexpandTriple___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ";"};
static const lean_object* l_Std_Internal_Do_unexpandTriple___closed__4 = (const lean_object*)&l_Std_Internal_Do_unexpandTriple___closed__4_value;
LEAN_EXPORT lean_object* l_Std_Internal_Do_unexpandTriple(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_unexpandTriple___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram(lean_object* v_c_28_){
_start:
{
lean_object* v___x_29_; uint8_t v___x_30_; 
v___x_29_ = ((lean_object*)(l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__4));
lean_inc(v_c_28_);
v___x_30_ = l_Lean_Syntax_isOfKind(v_c_28_, v___x_29_);
if (v___x_30_ == 0)
{
uint8_t v___x_31_; lean_object* v___x_32_; uint8_t v___x_33_; 
v___x_31_ = 1;
v___x_32_ = ((lean_object*)(l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__6));
lean_inc(v_c_28_);
v___x_33_ = l_Lean_Syntax_isOfKind(v_c_28_, v___x_32_);
if (v___x_33_ == 0)
{
lean_object* v___x_34_; uint8_t v___x_35_; 
v___x_34_ = ((lean_object*)(l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__8));
lean_inc(v_c_28_);
v___x_35_ = l_Lean_Syntax_isOfKind(v_c_28_, v___x_34_);
if (v___x_35_ == 0)
{
lean_object* v___x_36_; uint8_t v___x_37_; 
v___x_36_ = ((lean_object*)(l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__10));
lean_inc(v_c_28_);
v___x_37_ = l_Lean_Syntax_isOfKind(v_c_28_, v___x_36_);
if (v___x_37_ == 0)
{
lean_object* v___x_38_; uint8_t v___x_39_; 
v___x_38_ = ((lean_object*)(l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__12));
v___x_39_ = l_Lean_Syntax_isOfKind(v_c_28_, v___x_38_);
return v___x_39_;
}
else
{
lean_dec(v_c_28_);
return v___x_31_;
}
}
else
{
lean_dec(v_c_28_);
return v___x_31_;
}
}
else
{
lean_dec(v_c_28_);
return v___x_31_;
}
}
else
{
lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_40_ = lean_unsigned_to_nat(1u);
v___x_41_ = l_Lean_Syntax_getArg(v_c_28_, v___x_40_);
lean_dec(v_c_28_);
v_c_28_ = v___x_41_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___boxed(lean_object* v_c_43_){
_start:
{
uint8_t v_res_44_; lean_object* v_r_45_; 
v_res_44_ = l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram(v_c_43_);
v_r_45_ = lean_box(v_res_44_);
return v_r_45_;
}
}
static lean_object* _init_l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__8(void){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_63_ = ((lean_object*)(l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__7));
v___x_64_ = l_String_toRawSubstring_x27(v___x_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram(lean_object* v_c_118_, lean_object* v_m_x3f_119_, lean_object* v_a_120_, lean_object* v_a_121_){
_start:
{
if (lean_obj_tag(v_m_x3f_119_) == 0)
{
uint8_t v___x_122_; 
lean_inc(v_c_118_);
v___x_122_ = l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram(v_c_118_);
if (v___x_122_ == 0)
{
lean_object* v___x_123_; 
v___x_123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_123_, 0, v_c_118_);
lean_ctor_set(v___x_123_, 1, v_a_121_);
return v___x_123_;
}
else
{
lean_object* v_quotContext_124_; lean_object* v_currMacroScope_125_; lean_object* v_ref_126_; uint8_t v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v_quotContext_124_ = lean_ctor_get(v_a_120_, 1);
v_currMacroScope_125_ = lean_ctor_get(v_a_120_, 2);
v_ref_126_ = lean_ctor_get(v_a_120_, 5);
v___x_127_ = 0;
v___x_128_ = l_Lean_SourceInfo_fromRef(v_ref_126_, v___x_127_);
v___x_129_ = ((lean_object*)(l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__1));
v___x_130_ = ((lean_object*)(l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__3));
v___x_131_ = ((lean_object*)(l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__4));
lean_inc_n(v___x_128_, 15);
v___x_132_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_132_, 0, v___x_128_);
lean_ctor_set(v___x_132_, 1, v___x_131_);
v___x_133_ = ((lean_object*)(l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__6));
v___x_134_ = lean_obj_once(&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__8, &l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__8_once, _init_l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__8);
v___x_135_ = lean_box(0);
lean_inc(v_currMacroScope_125_);
lean_inc(v_quotContext_124_);
v___x_136_ = l_Lean_addMacroScope(v_quotContext_124_, v___x_135_, v_currMacroScope_125_);
v___x_137_ = ((lean_object*)(l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__21));
v___x_138_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_138_, 0, v___x_128_);
lean_ctor_set(v___x_138_, 1, v___x_134_);
lean_ctor_set(v___x_138_, 2, v___x_136_);
lean_ctor_set(v___x_138_, 3, v___x_137_);
v___x_139_ = l_Lean_Syntax_node1(v___x_128_, v___x_133_, v___x_138_);
v___x_140_ = l_Lean_Syntax_node2(v___x_128_, v___x_130_, v___x_132_, v___x_139_);
v___x_141_ = ((lean_object*)(l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__22));
v___x_142_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_142_, 0, v___x_128_);
lean_ctor_set(v___x_142_, 1, v___x_141_);
v___x_143_ = ((lean_object*)(l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__24));
v___x_144_ = ((lean_object*)(l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__26));
v___x_145_ = ((lean_object*)(l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__28));
v___x_146_ = ((lean_object*)(l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__29));
v___x_147_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_147_, 0, v___x_128_);
lean_ctor_set(v___x_147_, 1, v___x_146_);
v___x_148_ = l_Lean_Syntax_node1(v___x_128_, v___x_145_, v___x_147_);
v___x_149_ = ((lean_object*)(l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__31));
v___x_150_ = ((lean_object*)(l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__32));
v___x_151_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_151_, 0, v___x_128_);
lean_ctor_set(v___x_151_, 1, v___x_150_);
lean_inc_n(v___x_148_, 3);
v___x_152_ = l_Lean_Syntax_node3(v___x_128_, v___x_149_, v___x_148_, v___x_151_, v___x_148_);
v___x_153_ = l_Lean_Syntax_node1(v___x_128_, v___x_143_, v___x_152_);
v___x_154_ = ((lean_object*)(l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__33));
v___x_155_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_155_, 0, v___x_128_);
lean_ctor_set(v___x_155_, 1, v___x_154_);
lean_inc_ref(v___x_155_);
lean_inc_ref(v___x_142_);
lean_inc(v___x_140_);
v___x_156_ = l_Lean_Syntax_node5(v___x_128_, v___x_129_, v___x_140_, v___x_148_, v___x_142_, v___x_153_, v___x_155_);
v___x_157_ = l_Lean_Syntax_node1(v___x_128_, v___x_143_, v___x_148_);
v___x_158_ = l_Lean_Syntax_node2(v___x_128_, v___x_144_, v___x_156_, v___x_157_);
v___x_159_ = l_Lean_Syntax_node1(v___x_128_, v___x_143_, v___x_158_);
v___x_160_ = l_Lean_Syntax_node5(v___x_128_, v___x_129_, v___x_140_, v_c_118_, v___x_142_, v___x_159_, v___x_155_);
v___x_161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_161_, 0, v___x_160_);
lean_ctor_set(v___x_161_, 1, v_a_121_);
return v___x_161_;
}
}
else
{
lean_object* v_val_162_; lean_object* v_quotContext_163_; lean_object* v_currMacroScope_164_; lean_object* v_ref_165_; uint8_t v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v_val_162_ = lean_ctor_get(v_m_x3f_119_, 0);
lean_inc(v_val_162_);
lean_dec_ref_known(v_m_x3f_119_, 1);
v_quotContext_163_ = lean_ctor_get(v_a_120_, 1);
v_currMacroScope_164_ = lean_ctor_get(v_a_120_, 2);
v_ref_165_ = lean_ctor_get(v_a_120_, 5);
v___x_166_ = 0;
v___x_167_ = l_Lean_SourceInfo_fromRef(v_ref_165_, v___x_166_);
v___x_168_ = ((lean_object*)(l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__1));
v___x_169_ = ((lean_object*)(l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__3));
v___x_170_ = ((lean_object*)(l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__4));
lean_inc_n(v___x_167_, 11);
v___x_171_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_171_, 0, v___x_167_);
lean_ctor_set(v___x_171_, 1, v___x_170_);
v___x_172_ = ((lean_object*)(l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__6));
v___x_173_ = lean_obj_once(&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__8, &l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__8_once, _init_l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__8);
v___x_174_ = lean_box(0);
lean_inc(v_currMacroScope_164_);
lean_inc(v_quotContext_163_);
v___x_175_ = l_Lean_addMacroScope(v_quotContext_163_, v___x_174_, v_currMacroScope_164_);
v___x_176_ = ((lean_object*)(l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__21));
v___x_177_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_177_, 0, v___x_167_);
lean_ctor_set(v___x_177_, 1, v___x_173_);
lean_ctor_set(v___x_177_, 2, v___x_175_);
lean_ctor_set(v___x_177_, 3, v___x_176_);
v___x_178_ = l_Lean_Syntax_node1(v___x_167_, v___x_172_, v___x_177_);
v___x_179_ = l_Lean_Syntax_node2(v___x_167_, v___x_169_, v___x_171_, v___x_178_);
v___x_180_ = ((lean_object*)(l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__22));
v___x_181_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_181_, 0, v___x_167_);
lean_ctor_set(v___x_181_, 1, v___x_180_);
v___x_182_ = ((lean_object*)(l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__24));
v___x_183_ = ((lean_object*)(l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__26));
v___x_184_ = ((lean_object*)(l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__28));
v___x_185_ = ((lean_object*)(l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__29));
v___x_186_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_186_, 0, v___x_167_);
lean_ctor_set(v___x_186_, 1, v___x_185_);
v___x_187_ = l_Lean_Syntax_node1(v___x_167_, v___x_184_, v___x_186_);
v___x_188_ = l_Lean_Syntax_node1(v___x_167_, v___x_182_, v___x_187_);
v___x_189_ = l_Lean_Syntax_node2(v___x_167_, v___x_183_, v_val_162_, v___x_188_);
v___x_190_ = l_Lean_Syntax_node1(v___x_167_, v___x_182_, v___x_189_);
v___x_191_ = ((lean_object*)(l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__33));
v___x_192_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_192_, 0, v___x_167_);
lean_ctor_set(v___x_192_, 1, v___x_191_);
v___x_193_ = l_Lean_Syntax_node5(v___x_167_, v___x_168_, v___x_179_, v_c_118_, v___x_181_, v___x_190_, v___x_192_);
v___x_194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_194_, 0, v___x_193_);
lean_ctor_set(v___x_194_, 1, v_a_121_);
return v___x_194_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___boxed(lean_object* v_c_195_, lean_object* v_m_x3f_196_, lean_object* v_a_197_, lean_object* v_a_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram(v_c_195_, v_m_x3f_196_, v_a_197_, v_a_198_);
lean_dec_ref(v_a_197_);
return v_res_199_;
}
}
static lean_object* _init_l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__1(void){
_start:
{
lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_380_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__0));
v___x_381_ = l_String_toRawSubstring_x27(v___x_380_);
return v___x_381_;
}
}
static lean_object* _init_l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__9(void){
_start:
{
lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_401_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__8));
v___x_402_ = l_String_toRawSubstring_x27(v___x_401_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1(lean_object* v_x_417_, lean_object* v_a_418_, lean_object* v_a_419_){
_start:
{
lean_object* v___x_420_; uint8_t v___x_421_; 
v___x_420_ = ((lean_object*)(l_Std_Internal_Do_tripleNotation___closed__1));
lean_inc(v_x_417_);
v___x_421_ = l_Lean_Syntax_isOfKind(v_x_417_, v___x_420_);
if (v___x_421_ == 0)
{
lean_object* v___x_422_; lean_object* v___x_423_; 
lean_dec(v_x_417_);
v___x_422_ = lean_box(1);
v___x_423_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_423_, 0, v___x_422_);
lean_ctor_set(v___x_423_, 1, v_a_419_);
return v___x_423_;
}
else
{
lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v_m_427_; lean_object* v___y_428_; lean_object* v___y_429_; lean_object* v___x_463_; lean_object* v___x_464_; uint8_t v___x_465_; 
v___x_424_ = lean_unsigned_to_nat(1u);
v___x_425_ = l_Lean_Syntax_getArg(v_x_417_, v___x_424_);
v___x_463_ = lean_unsigned_to_nat(3u);
v___x_464_ = l_Lean_Syntax_getArg(v_x_417_, v___x_463_);
v___x_465_ = l_Lean_Syntax_isNone(v___x_464_);
if (v___x_465_ == 0)
{
lean_object* v___x_466_; uint8_t v___x_467_; 
v___x_466_ = lean_unsigned_to_nat(5u);
lean_inc(v___x_464_);
v___x_467_ = l_Lean_Syntax_matchesNull(v___x_464_, v___x_466_);
if (v___x_467_ == 0)
{
lean_object* v___x_468_; lean_object* v___x_469_; 
lean_dec(v___x_464_);
lean_dec(v___x_425_);
lean_dec(v_x_417_);
v___x_468_ = lean_box(1);
v___x_469_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_469_, 0, v___x_468_);
lean_ctor_set(v___x_469_, 1, v_a_419_);
return v___x_469_;
}
else
{
lean_object* v___x_470_; lean_object* v___x_471_; uint8_t v___x_472_; 
v___x_470_ = l_Lean_Syntax_getArg(v___x_464_, v___x_424_);
v___x_471_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__15));
v___x_472_ = l_Lean_Syntax_matchesIdent(v___x_470_, v___x_471_);
lean_dec(v___x_470_);
if (v___x_472_ == 0)
{
lean_object* v___x_473_; lean_object* v___x_474_; 
lean_dec(v___x_464_);
lean_dec(v___x_425_);
lean_dec(v_x_417_);
v___x_473_ = lean_box(1);
v___x_474_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_474_, 0, v___x_473_);
lean_ctor_set(v___x_474_, 1, v_a_419_);
return v___x_474_;
}
else
{
lean_object* v_m_475_; lean_object* v___x_476_; 
v_m_475_ = l_Lean_Syntax_getArg(v___x_464_, v___x_463_);
lean_dec(v___x_464_);
v___x_476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_476_, 0, v_m_475_);
v_m_427_ = v___x_476_;
v___y_428_ = v_a_418_;
v___y_429_ = v_a_419_;
goto v___jp_426_;
}
}
}
else
{
lean_object* v___x_477_; 
lean_dec(v___x_464_);
v___x_477_ = lean_box(0);
v_m_427_ = v___x_477_;
v___y_428_ = v_a_418_;
v___y_429_ = v_a_419_;
goto v___jp_426_;
}
v___jp_426_:
{
lean_object* v___x_430_; lean_object* v_c_431_; lean_object* v___x_432_; lean_object* v_a_433_; lean_object* v_a_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_462_; 
v___x_430_ = lean_unsigned_to_nat(4u);
v_c_431_ = l_Lean_Syntax_getArg(v_x_417_, v___x_430_);
v___x_432_ = l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram(v_c_431_, v_m_427_, v___y_428_, v___y_429_);
v_a_433_ = lean_ctor_get(v___x_432_, 0);
v_a_434_ = lean_ctor_get(v___x_432_, 1);
v_isSharedCheck_462_ = !lean_is_exclusive(v___x_432_);
if (v_isSharedCheck_462_ == 0)
{
v___x_436_ = v___x_432_;
v_isShared_437_ = v_isSharedCheck_462_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_a_434_);
lean_inc(v_a_433_);
lean_dec(v___x_432_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_462_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v_quotContext_438_; lean_object* v_currMacroScope_439_; lean_object* v_ref_440_; lean_object* v___x_441_; lean_object* v___x_442_; uint8_t v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_460_; 
v_quotContext_438_ = lean_ctor_get(v___y_428_, 1);
v_currMacroScope_439_ = lean_ctor_get(v___y_428_, 2);
v_ref_440_ = lean_ctor_get(v___y_428_, 5);
v___x_441_ = lean_unsigned_to_nat(6u);
v___x_442_ = l_Lean_Syntax_getArg(v_x_417_, v___x_441_);
lean_dec(v_x_417_);
v___x_443_ = 0;
v___x_444_ = l_Lean_SourceInfo_fromRef(v_ref_440_, v___x_443_);
v___x_445_ = ((lean_object*)(l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__26));
v___x_446_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__1, &l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__1_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__1);
v___x_447_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__2));
lean_inc_n(v_currMacroScope_439_, 2);
lean_inc_n(v_quotContext_438_, 2);
v___x_448_ = l_Lean_addMacroScope(v_quotContext_438_, v___x_447_, v_currMacroScope_439_);
v___x_449_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__7));
lean_inc_n(v___x_444_, 3);
v___x_450_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_450_, 0, v___x_444_);
lean_ctor_set(v___x_450_, 1, v___x_446_);
lean_ctor_set(v___x_450_, 2, v___x_448_);
lean_ctor_set(v___x_450_, 3, v___x_449_);
v___x_451_ = ((lean_object*)(l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__24));
v___x_452_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__9, &l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__9_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__9);
v___x_453_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__11));
v___x_454_ = l_Lean_addMacroScope(v_quotContext_438_, v___x_453_, v_currMacroScope_439_);
v___x_455_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__13));
v___x_456_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_456_, 0, v___x_444_);
lean_ctor_set(v___x_456_, 1, v___x_452_);
lean_ctor_set(v___x_456_, 2, v___x_454_);
lean_ctor_set(v___x_456_, 3, v___x_455_);
v___x_457_ = l_Lean_Syntax_node4(v___x_444_, v___x_451_, v_a_433_, v___x_425_, v___x_442_, v___x_456_);
v___x_458_ = l_Lean_Syntax_node2(v___x_444_, v___x_445_, v___x_450_, v___x_457_);
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 0, v___x_458_);
v___x_460_ = v___x_436_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v___x_458_);
lean_ctor_set(v_reuseFailAlloc_461_, 1, v_a_434_);
v___x_460_ = v_reuseFailAlloc_461_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
return v___x_460_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___boxed(lean_object* v_x_478_, lean_object* v_a_479_, lean_object* v_a_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1(v_x_478_, v_a_479_, v_a_480_);
lean_dec_ref(v_a_479_);
return v_res_481_;
}
}
static lean_object* _init_l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__6(void){
_start:
{
lean_object* v___x_500_; 
v___x_500_ = l_Array_mkArray0(lean_box(0));
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1(lean_object* v_x_502_, lean_object* v_a_503_, lean_object* v_a_504_){
_start:
{
lean_object* v___x_505_; uint8_t v___x_506_; 
v___x_505_ = ((lean_object*)(l_Std_Internal_Do_tripleBinderNotation___closed__1));
lean_inc(v_x_502_);
v___x_506_ = l_Lean_Syntax_isOfKind(v_x_502_, v___x_505_);
if (v___x_506_ == 0)
{
lean_object* v___x_507_; lean_object* v___x_508_; 
lean_dec(v_x_502_);
v___x_507_ = lean_box(1);
v___x_508_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_508_, 0, v___x_507_);
lean_ctor_set(v___x_508_, 1, v_a_504_);
return v___x_508_;
}
else
{
lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v_m_512_; lean_object* v___y_513_; lean_object* v___y_514_; lean_object* v___x_576_; lean_object* v___x_577_; uint8_t v___x_578_; 
v___x_509_ = lean_unsigned_to_nat(1u);
v___x_510_ = l_Lean_Syntax_getArg(v_x_502_, v___x_509_);
v___x_576_ = lean_unsigned_to_nat(3u);
v___x_577_ = l_Lean_Syntax_getArg(v_x_502_, v___x_576_);
v___x_578_ = l_Lean_Syntax_isNone(v___x_577_);
if (v___x_578_ == 0)
{
lean_object* v___x_579_; uint8_t v___x_580_; 
v___x_579_ = lean_unsigned_to_nat(5u);
lean_inc(v___x_577_);
v___x_580_ = l_Lean_Syntax_matchesNull(v___x_577_, v___x_579_);
if (v___x_580_ == 0)
{
lean_object* v___x_581_; lean_object* v___x_582_; 
lean_dec(v___x_577_);
lean_dec(v___x_510_);
lean_dec(v_x_502_);
v___x_581_ = lean_box(1);
v___x_582_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_582_, 0, v___x_581_);
lean_ctor_set(v___x_582_, 1, v_a_504_);
return v___x_582_;
}
else
{
lean_object* v___x_583_; lean_object* v___x_584_; uint8_t v___x_585_; 
v___x_583_ = l_Lean_Syntax_getArg(v___x_577_, v___x_509_);
v___x_584_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__15));
v___x_585_ = l_Lean_Syntax_matchesIdent(v___x_583_, v___x_584_);
lean_dec(v___x_583_);
if (v___x_585_ == 0)
{
lean_object* v___x_586_; lean_object* v___x_587_; 
lean_dec(v___x_577_);
lean_dec(v___x_510_);
lean_dec(v_x_502_);
v___x_586_ = lean_box(1);
v___x_587_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_587_, 0, v___x_586_);
lean_ctor_set(v___x_587_, 1, v_a_504_);
return v___x_587_;
}
else
{
lean_object* v_m_588_; lean_object* v___x_589_; 
v_m_588_ = l_Lean_Syntax_getArg(v___x_577_, v___x_576_);
lean_dec(v___x_577_);
v___x_589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_589_, 0, v_m_588_);
v_m_512_ = v___x_589_;
v___y_513_ = v_a_503_;
v___y_514_ = v_a_504_;
goto v___jp_511_;
}
}
}
else
{
lean_object* v___x_590_; 
lean_dec(v___x_577_);
v___x_590_ = lean_box(0);
v_m_512_ = v___x_590_;
v___y_513_ = v_a_503_;
v___y_514_ = v_a_504_;
goto v___jp_511_;
}
v___jp_511_:
{
lean_object* v___x_515_; lean_object* v_c_516_; lean_object* v___x_517_; lean_object* v_a_518_; lean_object* v_a_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_575_; 
v___x_515_ = lean_unsigned_to_nat(4u);
v_c_516_ = l_Lean_Syntax_getArg(v_x_502_, v___x_515_);
v___x_517_ = l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram(v_c_516_, v_m_512_, v___y_513_, v___y_514_);
v_a_518_ = lean_ctor_get(v___x_517_, 0);
v_a_519_ = lean_ctor_get(v___x_517_, 1);
v_isSharedCheck_575_ = !lean_is_exclusive(v___x_517_);
if (v_isSharedCheck_575_ == 0)
{
v___x_521_ = v___x_517_;
v_isShared_522_ = v_isSharedCheck_575_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_a_519_);
lean_inc(v_a_518_);
lean_dec(v___x_517_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_575_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v_quotContext_523_; lean_object* v_currMacroScope_524_; lean_object* v_ref_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; uint8_t v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_573_; 
v_quotContext_523_ = lean_ctor_get(v___y_513_, 1);
v_currMacroScope_524_ = lean_ctor_get(v___y_513_, 2);
v_ref_525_ = lean_ctor_get(v___y_513_, 5);
v___x_526_ = lean_unsigned_to_nat(6u);
v___x_527_ = l_Lean_Syntax_getArg(v_x_502_, v___x_526_);
v___x_528_ = lean_unsigned_to_nat(8u);
v___x_529_ = l_Lean_Syntax_getArg(v_x_502_, v___x_528_);
lean_dec(v_x_502_);
v___x_530_ = 0;
v___x_531_ = l_Lean_SourceInfo_fromRef(v_ref_525_, v___x_530_);
v___x_532_ = ((lean_object*)(l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__26));
v___x_533_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__1, &l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__1_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__1);
v___x_534_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__2));
lean_inc_n(v_currMacroScope_524_, 3);
lean_inc_n(v_quotContext_523_, 3);
v___x_535_ = l_Lean_addMacroScope(v_quotContext_523_, v___x_534_, v_currMacroScope_524_);
v___x_536_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__7));
lean_inc_n(v___x_531_, 15);
v___x_537_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_537_, 0, v___x_531_);
lean_ctor_set(v___x_537_, 1, v___x_533_);
lean_ctor_set(v___x_537_, 2, v___x_535_);
lean_ctor_set(v___x_537_, 3, v___x_536_);
v___x_538_ = ((lean_object*)(l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__24));
v___x_539_ = ((lean_object*)(l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__4));
v___x_540_ = ((lean_object*)(l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__3));
v___x_541_ = ((lean_object*)(l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__4));
v___x_542_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_542_, 0, v___x_531_);
lean_ctor_set(v___x_542_, 1, v___x_541_);
v___x_543_ = ((lean_object*)(l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__6));
v___x_544_ = lean_obj_once(&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__8, &l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__8_once, _init_l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__8);
v___x_545_ = lean_box(0);
v___x_546_ = l_Lean_addMacroScope(v_quotContext_523_, v___x_545_, v_currMacroScope_524_);
v___x_547_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__1));
v___x_548_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_548_, 0, v___x_531_);
lean_ctor_set(v___x_548_, 1, v___x_544_);
lean_ctor_set(v___x_548_, 2, v___x_546_);
lean_ctor_set(v___x_548_, 3, v___x_547_);
v___x_549_ = l_Lean_Syntax_node1(v___x_531_, v___x_543_, v___x_548_);
v___x_550_ = l_Lean_Syntax_node2(v___x_531_, v___x_540_, v___x_542_, v___x_549_);
v___x_551_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__2));
v___x_552_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__3));
v___x_553_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_553_, 0, v___x_531_);
lean_ctor_set(v___x_553_, 1, v___x_551_);
v___x_554_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__5));
v___x_555_ = l_Lean_Syntax_node1(v___x_531_, v___x_538_, v___x_527_);
v___x_556_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__6, &l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__6_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__6);
v___x_557_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_557_, 0, v___x_531_);
lean_ctor_set(v___x_557_, 1, v___x_538_);
lean_ctor_set(v___x_557_, 2, v___x_556_);
v___x_558_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__7));
v___x_559_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_559_, 0, v___x_531_);
lean_ctor_set(v___x_559_, 1, v___x_558_);
v___x_560_ = l_Lean_Syntax_node4(v___x_531_, v___x_554_, v___x_555_, v___x_557_, v___x_559_, v___x_529_);
v___x_561_ = l_Lean_Syntax_node2(v___x_531_, v___x_552_, v___x_553_, v___x_560_);
v___x_562_ = ((lean_object*)(l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__33));
v___x_563_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_563_, 0, v___x_531_);
lean_ctor_set(v___x_563_, 1, v___x_562_);
v___x_564_ = l_Lean_Syntax_node3(v___x_531_, v___x_539_, v___x_550_, v___x_561_, v___x_563_);
v___x_565_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__9, &l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__9_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__9);
v___x_566_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__11));
v___x_567_ = l_Lean_addMacroScope(v_quotContext_523_, v___x_566_, v_currMacroScope_524_);
v___x_568_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__13));
v___x_569_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_569_, 0, v___x_531_);
lean_ctor_set(v___x_569_, 1, v___x_565_);
lean_ctor_set(v___x_569_, 2, v___x_567_);
lean_ctor_set(v___x_569_, 3, v___x_568_);
v___x_570_ = l_Lean_Syntax_node4(v___x_531_, v___x_538_, v_a_518_, v___x_510_, v___x_564_, v___x_569_);
v___x_571_ = l_Lean_Syntax_node2(v___x_531_, v___x_532_, v___x_537_, v___x_570_);
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 0, v___x_571_);
v___x_573_ = v___x_521_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v___x_571_);
lean_ctor_set(v_reuseFailAlloc_574_, 1, v_a_519_);
v___x_573_ = v_reuseFailAlloc_574_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
return v___x_573_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___boxed(lean_object* v_x_591_, lean_object* v_a_592_, lean_object* v_a_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1(v_x_591_, v_a_592_, v_a_593_);
lean_dec_ref(v_a_592_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleEPost__1(lean_object* v_x_595_, lean_object* v_a_596_, lean_object* v_a_597_){
_start:
{
lean_object* v___x_598_; uint8_t v___x_599_; 
v___x_598_ = ((lean_object*)(l_Std_Internal_Do_tripleEPost___closed__1));
lean_inc(v_x_595_);
v___x_599_ = l_Lean_Syntax_isOfKind(v_x_595_, v___x_598_);
if (v___x_599_ == 0)
{
lean_object* v___x_600_; lean_object* v___x_601_; 
lean_dec(v_x_595_);
v___x_600_ = lean_box(1);
v___x_601_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_601_, 0, v___x_600_);
lean_ctor_set(v___x_601_, 1, v_a_597_);
return v___x_601_;
}
else
{
lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v_m_605_; lean_object* v___y_606_; lean_object* v___y_607_; lean_object* v___x_638_; lean_object* v___x_639_; uint8_t v___x_640_; 
v___x_602_ = lean_unsigned_to_nat(1u);
v___x_603_ = l_Lean_Syntax_getArg(v_x_595_, v___x_602_);
v___x_638_ = lean_unsigned_to_nat(3u);
v___x_639_ = l_Lean_Syntax_getArg(v_x_595_, v___x_638_);
v___x_640_ = l_Lean_Syntax_isNone(v___x_639_);
if (v___x_640_ == 0)
{
lean_object* v___x_641_; uint8_t v___x_642_; 
v___x_641_ = lean_unsigned_to_nat(5u);
lean_inc(v___x_639_);
v___x_642_ = l_Lean_Syntax_matchesNull(v___x_639_, v___x_641_);
if (v___x_642_ == 0)
{
lean_object* v___x_643_; lean_object* v___x_644_; 
lean_dec(v___x_639_);
lean_dec(v___x_603_);
lean_dec(v_x_595_);
v___x_643_ = lean_box(1);
v___x_644_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_644_, 0, v___x_643_);
lean_ctor_set(v___x_644_, 1, v_a_597_);
return v___x_644_;
}
else
{
lean_object* v___x_645_; lean_object* v___x_646_; uint8_t v___x_647_; 
v___x_645_ = l_Lean_Syntax_getArg(v___x_639_, v___x_602_);
v___x_646_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__15));
v___x_647_ = l_Lean_Syntax_matchesIdent(v___x_645_, v___x_646_);
lean_dec(v___x_645_);
if (v___x_647_ == 0)
{
lean_object* v___x_648_; lean_object* v___x_649_; 
lean_dec(v___x_639_);
lean_dec(v___x_603_);
lean_dec(v_x_595_);
v___x_648_ = lean_box(1);
v___x_649_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_649_, 0, v___x_648_);
lean_ctor_set(v___x_649_, 1, v_a_597_);
return v___x_649_;
}
else
{
lean_object* v_m_650_; lean_object* v___x_651_; 
v_m_650_ = l_Lean_Syntax_getArg(v___x_639_, v___x_638_);
lean_dec(v___x_639_);
v___x_651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_651_, 0, v_m_650_);
v_m_605_ = v___x_651_;
v___y_606_ = v_a_596_;
v___y_607_ = v_a_597_;
goto v___jp_604_;
}
}
}
else
{
lean_object* v___x_652_; 
lean_dec(v___x_639_);
v___x_652_ = lean_box(0);
v_m_605_ = v___x_652_;
v___y_606_ = v_a_596_;
v___y_607_ = v_a_597_;
goto v___jp_604_;
}
v___jp_604_:
{
lean_object* v___x_608_; lean_object* v_c_609_; lean_object* v___x_610_; lean_object* v_a_611_; lean_object* v_a_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_637_; 
v___x_608_ = lean_unsigned_to_nat(4u);
v_c_609_ = l_Lean_Syntax_getArg(v_x_595_, v___x_608_);
v___x_610_ = l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram(v_c_609_, v_m_605_, v___y_606_, v___y_607_);
v_a_611_ = lean_ctor_get(v___x_610_, 0);
v_a_612_ = lean_ctor_get(v___x_610_, 1);
v_isSharedCheck_637_ = !lean_is_exclusive(v___x_610_);
if (v_isSharedCheck_637_ == 0)
{
v___x_614_ = v___x_610_;
v_isShared_615_ = v_isSharedCheck_637_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_a_612_);
lean_inc(v_a_611_);
lean_dec(v___x_610_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_637_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v_quotContext_616_; lean_object* v_currMacroScope_617_; lean_object* v_ref_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; uint8_t v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_635_; 
v_quotContext_616_ = lean_ctor_get(v___y_606_, 1);
v_currMacroScope_617_ = lean_ctor_get(v___y_606_, 2);
v_ref_618_ = lean_ctor_get(v___y_606_, 5);
v___x_619_ = lean_unsigned_to_nat(6u);
v___x_620_ = l_Lean_Syntax_getArg(v_x_595_, v___x_619_);
v___x_621_ = lean_unsigned_to_nat(8u);
v___x_622_ = l_Lean_Syntax_getArg(v_x_595_, v___x_621_);
lean_dec(v_x_595_);
v___x_623_ = 0;
v___x_624_ = l_Lean_SourceInfo_fromRef(v_ref_618_, v___x_623_);
v___x_625_ = ((lean_object*)(l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__26));
v___x_626_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__1, &l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__1_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__1);
v___x_627_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__2));
lean_inc(v_currMacroScope_617_);
lean_inc(v_quotContext_616_);
v___x_628_ = l_Lean_addMacroScope(v_quotContext_616_, v___x_627_, v_currMacroScope_617_);
v___x_629_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__7));
lean_inc_n(v___x_624_, 2);
v___x_630_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_630_, 0, v___x_624_);
lean_ctor_set(v___x_630_, 1, v___x_626_);
lean_ctor_set(v___x_630_, 2, v___x_628_);
lean_ctor_set(v___x_630_, 3, v___x_629_);
v___x_631_ = ((lean_object*)(l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__24));
v___x_632_ = l_Lean_Syntax_node4(v___x_624_, v___x_631_, v_a_611_, v___x_603_, v___x_620_, v___x_622_);
v___x_633_ = l_Lean_Syntax_node2(v___x_624_, v___x_625_, v___x_630_, v___x_632_);
if (v_isShared_615_ == 0)
{
lean_ctor_set(v___x_614_, 0, v___x_633_);
v___x_635_ = v___x_614_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v___x_633_);
lean_ctor_set(v_reuseFailAlloc_636_, 1, v_a_612_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
return v___x_635_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleEPost__1___boxed(lean_object* v_x_653_, lean_object* v_a_654_, lean_object* v_a_655_){
_start:
{
lean_object* v_res_656_; 
v_res_656_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleEPost__1(v_x_653_, v_a_654_, v_a_655_);
lean_dec_ref(v_a_654_);
return v_res_656_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderEPost__1(lean_object* v_x_657_, lean_object* v_a_658_, lean_object* v_a_659_){
_start:
{
lean_object* v___x_660_; uint8_t v___x_661_; 
v___x_660_ = ((lean_object*)(l_Std_Internal_Do_tripleBinderEPost___closed__1));
lean_inc(v_x_657_);
v___x_661_ = l_Lean_Syntax_isOfKind(v_x_657_, v___x_660_);
if (v___x_661_ == 0)
{
lean_object* v___x_662_; lean_object* v___x_663_; 
lean_dec(v_x_657_);
v___x_662_ = lean_box(1);
v___x_663_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_663_, 0, v___x_662_);
lean_ctor_set(v___x_663_, 1, v_a_659_);
return v___x_663_;
}
else
{
lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v_m_667_; lean_object* v___y_668_; lean_object* v___y_669_; lean_object* v___x_728_; lean_object* v___x_729_; uint8_t v___x_730_; 
v___x_664_ = lean_unsigned_to_nat(1u);
v___x_665_ = l_Lean_Syntax_getArg(v_x_657_, v___x_664_);
v___x_728_ = lean_unsigned_to_nat(3u);
v___x_729_ = l_Lean_Syntax_getArg(v_x_657_, v___x_728_);
v___x_730_ = l_Lean_Syntax_isNone(v___x_729_);
if (v___x_730_ == 0)
{
lean_object* v___x_731_; uint8_t v___x_732_; 
v___x_731_ = lean_unsigned_to_nat(5u);
lean_inc(v___x_729_);
v___x_732_ = l_Lean_Syntax_matchesNull(v___x_729_, v___x_731_);
if (v___x_732_ == 0)
{
lean_object* v___x_733_; lean_object* v___x_734_; 
lean_dec(v___x_729_);
lean_dec(v___x_665_);
lean_dec(v_x_657_);
v___x_733_ = lean_box(1);
v___x_734_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_734_, 0, v___x_733_);
lean_ctor_set(v___x_734_, 1, v_a_659_);
return v___x_734_;
}
else
{
lean_object* v___x_735_; lean_object* v___x_736_; uint8_t v___x_737_; 
v___x_735_ = l_Lean_Syntax_getArg(v___x_729_, v___x_664_);
v___x_736_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__15));
v___x_737_ = l_Lean_Syntax_matchesIdent(v___x_735_, v___x_736_);
lean_dec(v___x_735_);
if (v___x_737_ == 0)
{
lean_object* v___x_738_; lean_object* v___x_739_; 
lean_dec(v___x_729_);
lean_dec(v___x_665_);
lean_dec(v_x_657_);
v___x_738_ = lean_box(1);
v___x_739_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_739_, 0, v___x_738_);
lean_ctor_set(v___x_739_, 1, v_a_659_);
return v___x_739_;
}
else
{
lean_object* v_m_740_; lean_object* v___x_741_; 
v_m_740_ = l_Lean_Syntax_getArg(v___x_729_, v___x_728_);
lean_dec(v___x_729_);
v___x_741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_741_, 0, v_m_740_);
v_m_667_ = v___x_741_;
v___y_668_ = v_a_658_;
v___y_669_ = v_a_659_;
goto v___jp_666_;
}
}
}
else
{
lean_object* v___x_742_; 
lean_dec(v___x_729_);
v___x_742_ = lean_box(0);
v_m_667_ = v___x_742_;
v___y_668_ = v_a_658_;
v___y_669_ = v_a_659_;
goto v___jp_666_;
}
v___jp_666_:
{
lean_object* v___x_670_; lean_object* v_c_671_; lean_object* v___x_672_; lean_object* v_a_673_; lean_object* v_a_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_727_; 
v___x_670_ = lean_unsigned_to_nat(4u);
v_c_671_ = l_Lean_Syntax_getArg(v_x_657_, v___x_670_);
v___x_672_ = l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram(v_c_671_, v_m_667_, v___y_668_, v___y_669_);
v_a_673_ = lean_ctor_get(v___x_672_, 0);
v_a_674_ = lean_ctor_get(v___x_672_, 1);
v_isSharedCheck_727_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_727_ == 0)
{
v___x_676_ = v___x_672_;
v_isShared_677_ = v_isSharedCheck_727_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_a_674_);
lean_inc(v_a_673_);
lean_dec(v___x_672_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_727_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v_quotContext_678_; lean_object* v_currMacroScope_679_; lean_object* v_ref_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; uint8_t v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_725_; 
v_quotContext_678_ = lean_ctor_get(v___y_668_, 1);
v_currMacroScope_679_ = lean_ctor_get(v___y_668_, 2);
v_ref_680_ = lean_ctor_get(v___y_668_, 5);
v___x_681_ = lean_unsigned_to_nat(6u);
v___x_682_ = l_Lean_Syntax_getArg(v_x_657_, v___x_681_);
v___x_683_ = lean_unsigned_to_nat(8u);
v___x_684_ = l_Lean_Syntax_getArg(v_x_657_, v___x_683_);
v___x_685_ = lean_unsigned_to_nat(10u);
v___x_686_ = l_Lean_Syntax_getArg(v_x_657_, v___x_685_);
lean_dec(v_x_657_);
v___x_687_ = 0;
v___x_688_ = l_Lean_SourceInfo_fromRef(v_ref_680_, v___x_687_);
v___x_689_ = ((lean_object*)(l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__26));
v___x_690_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__1, &l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__1_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__1);
v___x_691_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__2));
lean_inc_n(v_currMacroScope_679_, 2);
lean_inc_n(v_quotContext_678_, 2);
v___x_692_ = l_Lean_addMacroScope(v_quotContext_678_, v___x_691_, v_currMacroScope_679_);
v___x_693_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__7));
lean_inc_n(v___x_688_, 14);
v___x_694_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_694_, 0, v___x_688_);
lean_ctor_set(v___x_694_, 1, v___x_690_);
lean_ctor_set(v___x_694_, 2, v___x_692_);
lean_ctor_set(v___x_694_, 3, v___x_693_);
v___x_695_ = ((lean_object*)(l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__24));
v___x_696_ = ((lean_object*)(l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__4));
v___x_697_ = ((lean_object*)(l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__3));
v___x_698_ = ((lean_object*)(l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__4));
v___x_699_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_699_, 0, v___x_688_);
lean_ctor_set(v___x_699_, 1, v___x_698_);
v___x_700_ = ((lean_object*)(l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__6));
v___x_701_ = lean_obj_once(&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__8, &l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__8_once, _init_l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__8);
v___x_702_ = lean_box(0);
v___x_703_ = l_Lean_addMacroScope(v_quotContext_678_, v___x_702_, v_currMacroScope_679_);
v___x_704_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__1));
v___x_705_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_705_, 0, v___x_688_);
lean_ctor_set(v___x_705_, 1, v___x_701_);
lean_ctor_set(v___x_705_, 2, v___x_703_);
lean_ctor_set(v___x_705_, 3, v___x_704_);
v___x_706_ = l_Lean_Syntax_node1(v___x_688_, v___x_700_, v___x_705_);
v___x_707_ = l_Lean_Syntax_node2(v___x_688_, v___x_697_, v___x_699_, v___x_706_);
v___x_708_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__2));
v___x_709_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__3));
v___x_710_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_710_, 0, v___x_688_);
lean_ctor_set(v___x_710_, 1, v___x_708_);
v___x_711_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__5));
v___x_712_ = l_Lean_Syntax_node1(v___x_688_, v___x_695_, v___x_682_);
v___x_713_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__6, &l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__6_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__6);
v___x_714_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_714_, 0, v___x_688_);
lean_ctor_set(v___x_714_, 1, v___x_695_);
lean_ctor_set(v___x_714_, 2, v___x_713_);
v___x_715_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__7));
v___x_716_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_716_, 0, v___x_688_);
lean_ctor_set(v___x_716_, 1, v___x_715_);
v___x_717_ = l_Lean_Syntax_node4(v___x_688_, v___x_711_, v___x_712_, v___x_714_, v___x_716_, v___x_684_);
v___x_718_ = l_Lean_Syntax_node2(v___x_688_, v___x_709_, v___x_710_, v___x_717_);
v___x_719_ = ((lean_object*)(l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__33));
v___x_720_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_720_, 0, v___x_688_);
lean_ctor_set(v___x_720_, 1, v___x_719_);
v___x_721_ = l_Lean_Syntax_node3(v___x_688_, v___x_696_, v___x_707_, v___x_718_, v___x_720_);
v___x_722_ = l_Lean_Syntax_node4(v___x_688_, v___x_695_, v_a_673_, v___x_665_, v___x_721_, v___x_686_);
v___x_723_ = l_Lean_Syntax_node2(v___x_688_, v___x_689_, v___x_694_, v___x_722_);
if (v_isShared_677_ == 0)
{
lean_ctor_set(v___x_676_, 0, v___x_723_);
v___x_725_ = v___x_676_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v___x_723_);
lean_ctor_set(v_reuseFailAlloc_726_, 1, v_a_674_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderEPost__1___boxed(lean_object* v_x_743_, lean_object* v_a_744_, lean_object* v_a_745_){
_start:
{
lean_object* v_res_746_; 
v_res_746_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderEPost__1(v_x_743_, v_a_744_, v_a_745_);
lean_dec_ref(v_a_744_);
return v_res_746_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_unexpandTriple(lean_object* v_x_755_, lean_object* v_a_756_, lean_object* v_a_757_){
_start:
{
lean_object* v___x_758_; uint8_t v___x_759_; 
v___x_758_ = ((lean_object*)(l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__26));
lean_inc(v_x_755_);
v___x_759_ = l_Lean_Syntax_isOfKind(v_x_755_, v___x_758_);
if (v___x_759_ == 0)
{
lean_object* v___x_760_; lean_object* v___x_761_; 
lean_dec(v_x_755_);
v___x_760_ = lean_box(0);
v___x_761_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_761_, 0, v___x_760_);
lean_ctor_set(v___x_761_, 1, v_a_757_);
return v___x_761_;
}
else
{
lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; uint8_t v___x_765_; 
v___x_762_ = lean_unsigned_to_nat(1u);
v___x_763_ = l_Lean_Syntax_getArg(v_x_755_, v___x_762_);
lean_dec(v_x_755_);
v___x_764_ = lean_unsigned_to_nat(4u);
lean_inc(v___x_763_);
v___x_765_ = l_Lean_Syntax_matchesNull(v___x_763_, v___x_764_);
if (v___x_765_ == 0)
{
lean_object* v___x_766_; lean_object* v___x_767_; 
lean_dec(v___x_763_);
v___x_766_ = lean_box(0);
v___x_767_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_767_, 0, v___x_766_);
lean_ctor_set(v___x_767_, 1, v_a_757_);
return v___x_767_;
}
else
{
lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; uint8_t v___x_776_; 
v___x_768_ = lean_unsigned_to_nat(0u);
v___x_769_ = l_Lean_Syntax_getArg(v___x_763_, v___x_768_);
v___x_770_ = l_Lean_Syntax_getArg(v___x_763_, v___x_762_);
v___x_771_ = lean_unsigned_to_nat(2u);
v___x_772_ = l_Lean_Syntax_getArg(v___x_763_, v___x_771_);
v___x_773_ = lean_unsigned_to_nat(3u);
v___x_774_ = l_Lean_Syntax_getArg(v___x_763_, v___x_773_);
lean_dec(v___x_763_);
v___x_775_ = ((lean_object*)(l_Std_Internal_Do_unexpandTriple___closed__1));
lean_inc(v___x_774_);
v___x_776_ = l_Lean_Syntax_isOfKind(v___x_774_, v___x_775_);
if (v___x_776_ == 0)
{
lean_object* v___x_777_; uint8_t v___x_778_; 
v___x_777_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__11));
v___x_778_ = l_Lean_Syntax_matchesIdent(v___x_774_, v___x_777_);
if (v___x_778_ == 0)
{
lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_779_ = l_Lean_SourceInfo_fromRef(v_a_756_, v___x_778_);
v___x_780_ = ((lean_object*)(l_Std_Internal_Do_tripleEPost___closed__1));
v___x_781_ = ((lean_object*)(l_Std_Internal_Do_unexpandTriple___closed__2));
lean_inc_n(v___x_779_, 4);
v___x_782_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_782_, 0, v___x_779_);
lean_ctor_set(v___x_782_, 1, v___x_781_);
v___x_783_ = ((lean_object*)(l_Std_Internal_Do_unexpandTriple___closed__3));
v___x_784_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_784_, 0, v___x_779_);
lean_ctor_set(v___x_784_, 1, v___x_783_);
v___x_785_ = ((lean_object*)(l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__24));
v___x_786_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__6, &l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__6_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__6);
v___x_787_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_787_, 0, v___x_779_);
lean_ctor_set(v___x_787_, 1, v___x_785_);
lean_ctor_set(v___x_787_, 2, v___x_786_);
v___x_788_ = ((lean_object*)(l_Std_Internal_Do_unexpandTriple___closed__4));
v___x_789_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_789_, 0, v___x_779_);
lean_ctor_set(v___x_789_, 1, v___x_788_);
v___x_790_ = lean_unsigned_to_nat(10u);
v___x_791_ = lean_mk_empty_array_with_capacity(v___x_790_);
lean_inc_ref(v___x_782_);
v___x_792_ = lean_array_push(v___x_791_, v___x_782_);
v___x_793_ = lean_array_push(v___x_792_, v___x_770_);
lean_inc_ref(v___x_784_);
v___x_794_ = lean_array_push(v___x_793_, v___x_784_);
v___x_795_ = lean_array_push(v___x_794_, v___x_787_);
v___x_796_ = lean_array_push(v___x_795_, v___x_769_);
v___x_797_ = lean_array_push(v___x_796_, v___x_782_);
v___x_798_ = lean_array_push(v___x_797_, v___x_772_);
v___x_799_ = lean_array_push(v___x_798_, v___x_789_);
v___x_800_ = lean_array_push(v___x_799_, v___x_774_);
v___x_801_ = lean_array_push(v___x_800_, v___x_784_);
v___x_802_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_802_, 0, v___x_779_);
lean_ctor_set(v___x_802_, 1, v___x_780_);
lean_ctor_set(v___x_802_, 2, v___x_801_);
v___x_803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_803_, 0, v___x_802_);
lean_ctor_set(v___x_803_, 1, v_a_757_);
return v___x_803_;
}
else
{
lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; 
lean_dec(v___x_774_);
v___x_804_ = l_Lean_SourceInfo_fromRef(v_a_756_, v___x_776_);
v___x_805_ = ((lean_object*)(l_Std_Internal_Do_tripleNotation___closed__1));
v___x_806_ = ((lean_object*)(l_Std_Internal_Do_unexpandTriple___closed__2));
lean_inc_n(v___x_804_, 3);
v___x_807_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_807_, 0, v___x_804_);
lean_ctor_set(v___x_807_, 1, v___x_806_);
v___x_808_ = ((lean_object*)(l_Std_Internal_Do_unexpandTriple___closed__3));
v___x_809_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_809_, 0, v___x_804_);
lean_ctor_set(v___x_809_, 1, v___x_808_);
v___x_810_ = ((lean_object*)(l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__24));
v___x_811_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__6, &l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__6_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__6);
v___x_812_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_812_, 0, v___x_804_);
lean_ctor_set(v___x_812_, 1, v___x_810_);
lean_ctor_set(v___x_812_, 2, v___x_811_);
lean_inc_ref(v___x_809_);
lean_inc_ref(v___x_807_);
v___x_813_ = l_Lean_Syntax_node8(v___x_804_, v___x_805_, v___x_807_, v___x_770_, v___x_809_, v___x_812_, v___x_769_, v___x_807_, v___x_772_, v___x_809_);
v___x_814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_814_, 0, v___x_813_);
lean_ctor_set(v___x_814_, 1, v_a_757_);
return v___x_814_;
}
}
else
{
uint8_t v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; 
lean_dec(v___x_774_);
v___x_815_ = 0;
v___x_816_ = l_Lean_SourceInfo_fromRef(v_a_756_, v___x_815_);
v___x_817_ = ((lean_object*)(l_Std_Internal_Do_tripleNotation___closed__1));
v___x_818_ = ((lean_object*)(l_Std_Internal_Do_unexpandTriple___closed__2));
lean_inc_n(v___x_816_, 3);
v___x_819_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_819_, 0, v___x_816_);
lean_ctor_set(v___x_819_, 1, v___x_818_);
v___x_820_ = ((lean_object*)(l_Std_Internal_Do_unexpandTriple___closed__3));
v___x_821_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_821_, 0, v___x_816_);
lean_ctor_set(v___x_821_, 1, v___x_820_);
v___x_822_ = ((lean_object*)(l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__24));
v___x_823_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__6, &l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__6_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__6);
v___x_824_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_824_, 0, v___x_816_);
lean_ctor_set(v___x_824_, 1, v___x_822_);
lean_ctor_set(v___x_824_, 2, v___x_823_);
lean_inc_ref(v___x_821_);
lean_inc_ref(v___x_819_);
v___x_825_ = l_Lean_Syntax_node8(v___x_816_, v___x_817_, v___x_819_, v___x_770_, v___x_821_, v___x_824_, v___x_769_, v___x_819_, v___x_772_, v___x_821_);
v___x_826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_826_, 0, v___x_825_);
lean_ctor_set(v___x_826_, 1, v_a_757_);
return v___x_826_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_unexpandTriple___boxed(lean_object* v_x_827_, lean_object* v_a_828_, lean_object* v_a_829_){
_start:
{
lean_object* v_res_830_; 
v_res_830_ = l_Std_Internal_Do_unexpandTriple(v_x_827_, v_a_828_, v_a_829_);
lean_dec(v_a_828_);
return v_res_830_;
}
}
lean_object* runtime_initialize_Std_Internal_Do_WP(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Do_ExceptPost(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Internal_Do_Triple_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Internal_Do_WP(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Do_ExceptPost(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Internal_Do_Triple_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Internal_Do_WP(uint8_t builtin);
lean_object* initialize_Std_Internal_Do_ExceptPost(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Internal_Do_Triple_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Internal_Do_WP(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Do_ExceptPost(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Do_Triple_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Internal_Do_Triple_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Internal_Do_Triple_Basic(builtin);
}
#ifdef __cplusplus
}
#endif

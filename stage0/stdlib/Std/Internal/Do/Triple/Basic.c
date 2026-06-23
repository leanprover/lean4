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
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
lean_object* l_Lean_Syntax_SepArray_ofElems(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
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
static const lean_ctor_object l_Std_Internal_Do_tripleEPost___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 11}, .m_objs = {((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__8_value),((lean_object*)&l_Std_Internal_Do_tripleEPost___closed__2_value),((lean_object*)&l_Std_Internal_Do_tripleEPost___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Internal_Do_tripleEPost___closed__5 = (const lean_object*)&l_Std_Internal_Do_tripleEPost___closed__5_value;
static const lean_ctor_object l_Std_Internal_Do_tripleEPost___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__3_value),((lean_object*)&l_Std_Internal_Do_tripleEPost___closed__4_value),((lean_object*)&l_Std_Internal_Do_tripleEPost___closed__5_value)}};
static const lean_object* l_Std_Internal_Do_tripleEPost___closed__6 = (const lean_object*)&l_Std_Internal_Do_tripleEPost___closed__6_value;
static const lean_ctor_object l_Std_Internal_Do_tripleEPost___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__3_value),((lean_object*)&l_Std_Internal_Do_tripleEPost___closed__6_value),((lean_object*)&l_Std_Internal_Do_tripleNotation___closed__37_value)}};
static const lean_object* l_Std_Internal_Do_tripleEPost___closed__7 = (const lean_object*)&l_Std_Internal_Do_tripleEPost___closed__7_value;
static const lean_ctor_object l_Std_Internal_Do_tripleEPost___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_Do_tripleEPost___closed__1_value),((lean_object*)(((size_t)(60) << 1) | 1)),((lean_object*)&l_Std_Internal_Do_tripleEPost___closed__7_value)}};
static const lean_object* l_Std_Internal_Do_tripleEPost___closed__8 = (const lean_object*)&l_Std_Internal_Do_tripleEPost___closed__8_value;
LEAN_EXPORT const lean_object* l_Std_Internal_Do_tripleEPost = (const lean_object*)&l_Std_Internal_Do_tripleEPost___closed__8_value;
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
static const lean_string_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleEPost__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 12, .m_data = "termEpost⟨_⟩"};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleEPost__1___closed__0 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleEPost__1___closed__0_value;
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleEPost__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__9_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleEPost__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleEPost__1___closed__1_value_aux_0),((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__10_value),LEAN_SCALAR_PTR_LITERAL(225, 148, 172, 135, 227, 248, 47, 24)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleEPost__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleEPost__1___closed__1_value_aux_1),((lean_object*)&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__11_value),LEAN_SCALAR_PTR_LITERAL(165, 204, 33, 109, 120, 201, 43, 17)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleEPost__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleEPost__1___closed__1_value_aux_2),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleEPost__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 191, 145, 121, 242, 68, 46, 80)}};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleEPost__1___closed__1 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleEPost__1___closed__1_value;
static const lean_string_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleEPost__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 6, .m_data = "epost⟨"};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleEPost__1___closed__2 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleEPost__1___closed__2_value;
static const lean_string_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleEPost__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleEPost__1___closed__3 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleEPost__1___closed__3_value;
static const lean_string_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleEPost__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟩"};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleEPost__1___closed__4 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleEPost__1___closed__4_value;
LEAN_EXPORT lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleEPost__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleEPost__1___boxed(lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_362_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__0));
v___x_363_ = l_String_toRawSubstring_x27(v___x_362_);
return v___x_363_;
}
}
static lean_object* _init_l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__9(void){
_start:
{
lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_383_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__8));
v___x_384_ = l_String_toRawSubstring_x27(v___x_383_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1(lean_object* v_x_399_, lean_object* v_a_400_, lean_object* v_a_401_){
_start:
{
lean_object* v___x_402_; uint8_t v___x_403_; 
v___x_402_ = ((lean_object*)(l_Std_Internal_Do_tripleNotation___closed__1));
lean_inc(v_x_399_);
v___x_403_ = l_Lean_Syntax_isOfKind(v_x_399_, v___x_402_);
if (v___x_403_ == 0)
{
lean_object* v___x_404_; lean_object* v___x_405_; 
lean_dec(v_x_399_);
v___x_404_ = lean_box(1);
v___x_405_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_405_, 0, v___x_404_);
lean_ctor_set(v___x_405_, 1, v_a_401_);
return v___x_405_;
}
else
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v_m_409_; lean_object* v___y_410_; lean_object* v___y_411_; lean_object* v___x_445_; lean_object* v___x_446_; uint8_t v___x_447_; 
v___x_406_ = lean_unsigned_to_nat(1u);
v___x_407_ = l_Lean_Syntax_getArg(v_x_399_, v___x_406_);
v___x_445_ = lean_unsigned_to_nat(3u);
v___x_446_ = l_Lean_Syntax_getArg(v_x_399_, v___x_445_);
v___x_447_ = l_Lean_Syntax_isNone(v___x_446_);
if (v___x_447_ == 0)
{
lean_object* v___x_448_; uint8_t v___x_449_; 
v___x_448_ = lean_unsigned_to_nat(5u);
lean_inc(v___x_446_);
v___x_449_ = l_Lean_Syntax_matchesNull(v___x_446_, v___x_448_);
if (v___x_449_ == 0)
{
lean_object* v___x_450_; lean_object* v___x_451_; 
lean_dec(v___x_446_);
lean_dec(v___x_407_);
lean_dec(v_x_399_);
v___x_450_ = lean_box(1);
v___x_451_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_451_, 0, v___x_450_);
lean_ctor_set(v___x_451_, 1, v_a_401_);
return v___x_451_;
}
else
{
lean_object* v___x_452_; lean_object* v___x_453_; uint8_t v___x_454_; 
v___x_452_ = l_Lean_Syntax_getArg(v___x_446_, v___x_406_);
v___x_453_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__15));
v___x_454_ = l_Lean_Syntax_matchesIdent(v___x_452_, v___x_453_);
lean_dec(v___x_452_);
if (v___x_454_ == 0)
{
lean_object* v___x_455_; lean_object* v___x_456_; 
lean_dec(v___x_446_);
lean_dec(v___x_407_);
lean_dec(v_x_399_);
v___x_455_ = lean_box(1);
v___x_456_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_456_, 0, v___x_455_);
lean_ctor_set(v___x_456_, 1, v_a_401_);
return v___x_456_;
}
else
{
lean_object* v_m_457_; lean_object* v___x_458_; 
v_m_457_ = l_Lean_Syntax_getArg(v___x_446_, v___x_445_);
lean_dec(v___x_446_);
v___x_458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_458_, 0, v_m_457_);
v_m_409_ = v___x_458_;
v___y_410_ = v_a_400_;
v___y_411_ = v_a_401_;
goto v___jp_408_;
}
}
}
else
{
lean_object* v___x_459_; 
lean_dec(v___x_446_);
v___x_459_ = lean_box(0);
v_m_409_ = v___x_459_;
v___y_410_ = v_a_400_;
v___y_411_ = v_a_401_;
goto v___jp_408_;
}
v___jp_408_:
{
lean_object* v___x_412_; lean_object* v_c_413_; lean_object* v___x_414_; lean_object* v_a_415_; lean_object* v_a_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_444_; 
v___x_412_ = lean_unsigned_to_nat(4u);
v_c_413_ = l_Lean_Syntax_getArg(v_x_399_, v___x_412_);
v___x_414_ = l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram(v_c_413_, v_m_409_, v___y_410_, v___y_411_);
v_a_415_ = lean_ctor_get(v___x_414_, 0);
v_a_416_ = lean_ctor_get(v___x_414_, 1);
v_isSharedCheck_444_ = !lean_is_exclusive(v___x_414_);
if (v_isSharedCheck_444_ == 0)
{
v___x_418_ = v___x_414_;
v_isShared_419_ = v_isSharedCheck_444_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_a_416_);
lean_inc(v_a_415_);
lean_dec(v___x_414_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_444_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v_quotContext_420_; lean_object* v_currMacroScope_421_; lean_object* v_ref_422_; lean_object* v___x_423_; lean_object* v___x_424_; uint8_t v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_442_; 
v_quotContext_420_ = lean_ctor_get(v___y_410_, 1);
v_currMacroScope_421_ = lean_ctor_get(v___y_410_, 2);
v_ref_422_ = lean_ctor_get(v___y_410_, 5);
v___x_423_ = lean_unsigned_to_nat(6u);
v___x_424_ = l_Lean_Syntax_getArg(v_x_399_, v___x_423_);
lean_dec(v_x_399_);
v___x_425_ = 0;
v___x_426_ = l_Lean_SourceInfo_fromRef(v_ref_422_, v___x_425_);
v___x_427_ = ((lean_object*)(l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__26));
v___x_428_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__1, &l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__1_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__1);
v___x_429_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__2));
lean_inc_n(v_currMacroScope_421_, 2);
lean_inc_n(v_quotContext_420_, 2);
v___x_430_ = l_Lean_addMacroScope(v_quotContext_420_, v___x_429_, v_currMacroScope_421_);
v___x_431_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__7));
lean_inc_n(v___x_426_, 3);
v___x_432_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_432_, 0, v___x_426_);
lean_ctor_set(v___x_432_, 1, v___x_428_);
lean_ctor_set(v___x_432_, 2, v___x_430_);
lean_ctor_set(v___x_432_, 3, v___x_431_);
v___x_433_ = ((lean_object*)(l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__24));
v___x_434_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__9, &l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__9_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__9);
v___x_435_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__11));
v___x_436_ = l_Lean_addMacroScope(v_quotContext_420_, v___x_435_, v_currMacroScope_421_);
v___x_437_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__13));
v___x_438_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_438_, 0, v___x_426_);
lean_ctor_set(v___x_438_, 1, v___x_434_);
lean_ctor_set(v___x_438_, 2, v___x_436_);
lean_ctor_set(v___x_438_, 3, v___x_437_);
v___x_439_ = l_Lean_Syntax_node4(v___x_426_, v___x_433_, v_a_415_, v___x_407_, v___x_424_, v___x_438_);
v___x_440_ = l_Lean_Syntax_node2(v___x_426_, v___x_427_, v___x_432_, v___x_439_);
if (v_isShared_419_ == 0)
{
lean_ctor_set(v___x_418_, 0, v___x_440_);
v___x_442_ = v___x_418_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v___x_440_);
lean_ctor_set(v_reuseFailAlloc_443_, 1, v_a_416_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___boxed(lean_object* v_x_460_, lean_object* v_a_461_, lean_object* v_a_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1(v_x_460_, v_a_461_, v_a_462_);
lean_dec_ref(v_a_461_);
return v_res_463_;
}
}
static lean_object* _init_l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__6(void){
_start:
{
lean_object* v___x_482_; 
v___x_482_ = l_Array_mkArray0(lean_box(0));
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1(lean_object* v_x_484_, lean_object* v_a_485_, lean_object* v_a_486_){
_start:
{
lean_object* v___x_487_; uint8_t v___x_488_; 
v___x_487_ = ((lean_object*)(l_Std_Internal_Do_tripleBinderNotation___closed__1));
lean_inc(v_x_484_);
v___x_488_ = l_Lean_Syntax_isOfKind(v_x_484_, v___x_487_);
if (v___x_488_ == 0)
{
lean_object* v___x_489_; lean_object* v___x_490_; 
lean_dec(v_x_484_);
v___x_489_ = lean_box(1);
v___x_490_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_490_, 0, v___x_489_);
lean_ctor_set(v___x_490_, 1, v_a_486_);
return v___x_490_;
}
else
{
lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v_m_494_; lean_object* v___y_495_; lean_object* v___y_496_; lean_object* v___x_558_; lean_object* v___x_559_; uint8_t v___x_560_; 
v___x_491_ = lean_unsigned_to_nat(1u);
v___x_492_ = l_Lean_Syntax_getArg(v_x_484_, v___x_491_);
v___x_558_ = lean_unsigned_to_nat(3u);
v___x_559_ = l_Lean_Syntax_getArg(v_x_484_, v___x_558_);
v___x_560_ = l_Lean_Syntax_isNone(v___x_559_);
if (v___x_560_ == 0)
{
lean_object* v___x_561_; uint8_t v___x_562_; 
v___x_561_ = lean_unsigned_to_nat(5u);
lean_inc(v___x_559_);
v___x_562_ = l_Lean_Syntax_matchesNull(v___x_559_, v___x_561_);
if (v___x_562_ == 0)
{
lean_object* v___x_563_; lean_object* v___x_564_; 
lean_dec(v___x_559_);
lean_dec(v___x_492_);
lean_dec(v_x_484_);
v___x_563_ = lean_box(1);
v___x_564_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_564_, 0, v___x_563_);
lean_ctor_set(v___x_564_, 1, v_a_486_);
return v___x_564_;
}
else
{
lean_object* v___x_565_; lean_object* v___x_566_; uint8_t v___x_567_; 
v___x_565_ = l_Lean_Syntax_getArg(v___x_559_, v___x_491_);
v___x_566_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__15));
v___x_567_ = l_Lean_Syntax_matchesIdent(v___x_565_, v___x_566_);
lean_dec(v___x_565_);
if (v___x_567_ == 0)
{
lean_object* v___x_568_; lean_object* v___x_569_; 
lean_dec(v___x_559_);
lean_dec(v___x_492_);
lean_dec(v_x_484_);
v___x_568_ = lean_box(1);
v___x_569_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_569_, 0, v___x_568_);
lean_ctor_set(v___x_569_, 1, v_a_486_);
return v___x_569_;
}
else
{
lean_object* v_m_570_; lean_object* v___x_571_; 
v_m_570_ = l_Lean_Syntax_getArg(v___x_559_, v___x_558_);
lean_dec(v___x_559_);
v___x_571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_571_, 0, v_m_570_);
v_m_494_ = v___x_571_;
v___y_495_ = v_a_485_;
v___y_496_ = v_a_486_;
goto v___jp_493_;
}
}
}
else
{
lean_object* v___x_572_; 
lean_dec(v___x_559_);
v___x_572_ = lean_box(0);
v_m_494_ = v___x_572_;
v___y_495_ = v_a_485_;
v___y_496_ = v_a_486_;
goto v___jp_493_;
}
v___jp_493_:
{
lean_object* v___x_497_; lean_object* v_c_498_; lean_object* v___x_499_; lean_object* v_a_500_; lean_object* v_a_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_557_; 
v___x_497_ = lean_unsigned_to_nat(4u);
v_c_498_ = l_Lean_Syntax_getArg(v_x_484_, v___x_497_);
v___x_499_ = l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram(v_c_498_, v_m_494_, v___y_495_, v___y_496_);
v_a_500_ = lean_ctor_get(v___x_499_, 0);
v_a_501_ = lean_ctor_get(v___x_499_, 1);
v_isSharedCheck_557_ = !lean_is_exclusive(v___x_499_);
if (v_isSharedCheck_557_ == 0)
{
v___x_503_ = v___x_499_;
v_isShared_504_ = v_isSharedCheck_557_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_a_501_);
lean_inc(v_a_500_);
lean_dec(v___x_499_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_557_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v_quotContext_505_; lean_object* v_currMacroScope_506_; lean_object* v_ref_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; uint8_t v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_555_; 
v_quotContext_505_ = lean_ctor_get(v___y_495_, 1);
v_currMacroScope_506_ = lean_ctor_get(v___y_495_, 2);
v_ref_507_ = lean_ctor_get(v___y_495_, 5);
v___x_508_ = lean_unsigned_to_nat(6u);
v___x_509_ = l_Lean_Syntax_getArg(v_x_484_, v___x_508_);
v___x_510_ = lean_unsigned_to_nat(8u);
v___x_511_ = l_Lean_Syntax_getArg(v_x_484_, v___x_510_);
lean_dec(v_x_484_);
v___x_512_ = 0;
v___x_513_ = l_Lean_SourceInfo_fromRef(v_ref_507_, v___x_512_);
v___x_514_ = ((lean_object*)(l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__26));
v___x_515_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__1, &l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__1_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__1);
v___x_516_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__2));
lean_inc_n(v_currMacroScope_506_, 3);
lean_inc_n(v_quotContext_505_, 3);
v___x_517_ = l_Lean_addMacroScope(v_quotContext_505_, v___x_516_, v_currMacroScope_506_);
v___x_518_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__7));
lean_inc_n(v___x_513_, 15);
v___x_519_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_519_, 0, v___x_513_);
lean_ctor_set(v___x_519_, 1, v___x_515_);
lean_ctor_set(v___x_519_, 2, v___x_517_);
lean_ctor_set(v___x_519_, 3, v___x_518_);
v___x_520_ = ((lean_object*)(l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__24));
v___x_521_ = ((lean_object*)(l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_isSplitProgram___closed__4));
v___x_522_ = ((lean_object*)(l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__3));
v___x_523_ = ((lean_object*)(l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__4));
v___x_524_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_524_, 0, v___x_513_);
lean_ctor_set(v___x_524_, 1, v___x_523_);
v___x_525_ = ((lean_object*)(l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__6));
v___x_526_ = lean_obj_once(&l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__8, &l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__8_once, _init_l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__8);
v___x_527_ = lean_box(0);
v___x_528_ = l_Lean_addMacroScope(v_quotContext_505_, v___x_527_, v_currMacroScope_506_);
v___x_529_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__1));
v___x_530_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_530_, 0, v___x_513_);
lean_ctor_set(v___x_530_, 1, v___x_526_);
lean_ctor_set(v___x_530_, 2, v___x_528_);
lean_ctor_set(v___x_530_, 3, v___x_529_);
v___x_531_ = l_Lean_Syntax_node1(v___x_513_, v___x_525_, v___x_530_);
v___x_532_ = l_Lean_Syntax_node2(v___x_513_, v___x_522_, v___x_524_, v___x_531_);
v___x_533_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__2));
v___x_534_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__3));
v___x_535_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_535_, 0, v___x_513_);
lean_ctor_set(v___x_535_, 1, v___x_533_);
v___x_536_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__5));
v___x_537_ = l_Lean_Syntax_node1(v___x_513_, v___x_520_, v___x_509_);
v___x_538_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__6, &l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__6_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__6);
v___x_539_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_539_, 0, v___x_513_);
lean_ctor_set(v___x_539_, 1, v___x_520_);
lean_ctor_set(v___x_539_, 2, v___x_538_);
v___x_540_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__7));
v___x_541_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_541_, 0, v___x_513_);
lean_ctor_set(v___x_541_, 1, v___x_540_);
v___x_542_ = l_Lean_Syntax_node4(v___x_513_, v___x_536_, v___x_537_, v___x_539_, v___x_541_, v___x_511_);
v___x_543_ = l_Lean_Syntax_node2(v___x_513_, v___x_534_, v___x_535_, v___x_542_);
v___x_544_ = ((lean_object*)(l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__33));
v___x_545_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_545_, 0, v___x_513_);
lean_ctor_set(v___x_545_, 1, v___x_544_);
v___x_546_ = l_Lean_Syntax_node3(v___x_513_, v___x_521_, v___x_532_, v___x_543_, v___x_545_);
v___x_547_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__9, &l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__9_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__9);
v___x_548_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__11));
v___x_549_ = l_Lean_addMacroScope(v_quotContext_505_, v___x_548_, v_currMacroScope_506_);
v___x_550_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__13));
v___x_551_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_551_, 0, v___x_513_);
lean_ctor_set(v___x_551_, 1, v___x_547_);
lean_ctor_set(v___x_551_, 2, v___x_549_);
lean_ctor_set(v___x_551_, 3, v___x_550_);
v___x_552_ = l_Lean_Syntax_node4(v___x_513_, v___x_520_, v_a_500_, v___x_492_, v___x_546_, v___x_551_);
v___x_553_ = l_Lean_Syntax_node2(v___x_513_, v___x_514_, v___x_519_, v___x_552_);
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 0, v___x_553_);
v___x_555_ = v___x_503_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v___x_553_);
lean_ctor_set(v_reuseFailAlloc_556_, 1, v_a_501_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
return v___x_555_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___boxed(lean_object* v_x_573_, lean_object* v_a_574_, lean_object* v_a_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1(v_x_573_, v_a_574_, v_a_575_);
lean_dec_ref(v_a_574_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleEPost__1(lean_object* v_x_586_, lean_object* v_a_587_, lean_object* v_a_588_){
_start:
{
lean_object* v___x_589_; uint8_t v___x_590_; 
v___x_589_ = ((lean_object*)(l_Std_Internal_Do_tripleEPost___closed__1));
lean_inc(v_x_586_);
v___x_590_ = l_Lean_Syntax_isOfKind(v_x_586_, v___x_589_);
if (v___x_590_ == 0)
{
lean_object* v___x_591_; lean_object* v___x_592_; 
lean_dec(v_x_586_);
v___x_591_ = lean_box(1);
v___x_592_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_592_, 0, v___x_591_);
lean_ctor_set(v___x_592_, 1, v_a_588_);
return v___x_592_;
}
else
{
lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v_m_596_; lean_object* v___y_597_; lean_object* v___y_598_; lean_object* v___x_642_; lean_object* v___x_643_; uint8_t v___x_644_; 
v___x_593_ = lean_unsigned_to_nat(1u);
v___x_594_ = l_Lean_Syntax_getArg(v_x_586_, v___x_593_);
v___x_642_ = lean_unsigned_to_nat(3u);
v___x_643_ = l_Lean_Syntax_getArg(v_x_586_, v___x_642_);
v___x_644_ = l_Lean_Syntax_isNone(v___x_643_);
if (v___x_644_ == 0)
{
lean_object* v___x_645_; uint8_t v___x_646_; 
v___x_645_ = lean_unsigned_to_nat(5u);
lean_inc(v___x_643_);
v___x_646_ = l_Lean_Syntax_matchesNull(v___x_643_, v___x_645_);
if (v___x_646_ == 0)
{
lean_object* v___x_647_; lean_object* v___x_648_; 
lean_dec(v___x_643_);
lean_dec(v___x_594_);
lean_dec(v_x_586_);
v___x_647_ = lean_box(1);
v___x_648_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_648_, 0, v___x_647_);
lean_ctor_set(v___x_648_, 1, v_a_588_);
return v___x_648_;
}
else
{
lean_object* v___x_649_; lean_object* v___x_650_; uint8_t v___x_651_; 
v___x_649_ = l_Lean_Syntax_getArg(v___x_643_, v___x_593_);
v___x_650_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__15));
v___x_651_ = l_Lean_Syntax_matchesIdent(v___x_649_, v___x_650_);
lean_dec(v___x_649_);
if (v___x_651_ == 0)
{
lean_object* v___x_652_; lean_object* v___x_653_; 
lean_dec(v___x_643_);
lean_dec(v___x_594_);
lean_dec(v_x_586_);
v___x_652_ = lean_box(1);
v___x_653_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_653_, 0, v___x_652_);
lean_ctor_set(v___x_653_, 1, v_a_588_);
return v___x_653_;
}
else
{
lean_object* v_m_654_; lean_object* v___x_655_; 
v_m_654_ = l_Lean_Syntax_getArg(v___x_643_, v___x_642_);
lean_dec(v___x_643_);
v___x_655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_655_, 0, v_m_654_);
v_m_596_ = v___x_655_;
v___y_597_ = v_a_587_;
v___y_598_ = v_a_588_;
goto v___jp_595_;
}
}
}
else
{
lean_object* v___x_656_; 
lean_dec(v___x_643_);
v___x_656_ = lean_box(0);
v_m_596_ = v___x_656_;
v___y_597_ = v_a_587_;
v___y_598_ = v_a_588_;
goto v___jp_595_;
}
v___jp_595_:
{
lean_object* v___x_599_; lean_object* v_c_600_; lean_object* v___x_601_; lean_object* v_a_602_; lean_object* v_a_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_641_; 
v___x_599_ = lean_unsigned_to_nat(4u);
v_c_600_ = l_Lean_Syntax_getArg(v_x_586_, v___x_599_);
v___x_601_ = l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram(v_c_600_, v_m_596_, v___y_597_, v___y_598_);
v_a_602_ = lean_ctor_get(v___x_601_, 0);
v_a_603_ = lean_ctor_get(v___x_601_, 1);
v_isSharedCheck_641_ = !lean_is_exclusive(v___x_601_);
if (v_isSharedCheck_641_ == 0)
{
v___x_605_ = v___x_601_;
v_isShared_606_ = v_isSharedCheck_641_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_a_603_);
lean_inc(v_a_602_);
lean_dec(v___x_601_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_641_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v_quotContext_607_; lean_object* v_currMacroScope_608_; lean_object* v_ref_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v_Es_612_; lean_object* v___x_613_; lean_object* v___x_614_; uint8_t v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_639_; 
v_quotContext_607_ = lean_ctor_get(v___y_597_, 1);
v_currMacroScope_608_ = lean_ctor_get(v___y_597_, 2);
v_ref_609_ = lean_ctor_get(v___y_597_, 5);
v___x_610_ = lean_unsigned_to_nat(8u);
v___x_611_ = l_Lean_Syntax_getArg(v_x_586_, v___x_610_);
v_Es_612_ = l_Lean_Syntax_getArgs(v___x_611_);
lean_dec(v___x_611_);
v___x_613_ = lean_unsigned_to_nat(6u);
v___x_614_ = l_Lean_Syntax_getArg(v_x_586_, v___x_613_);
lean_dec(v_x_586_);
v___x_615_ = 0;
v___x_616_ = l_Lean_SourceInfo_fromRef(v_ref_609_, v___x_615_);
v___x_617_ = ((lean_object*)(l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__26));
v___x_618_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__1, &l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__1_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__1);
v___x_619_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__2));
lean_inc(v_currMacroScope_608_);
lean_inc(v_quotContext_607_);
v___x_620_ = l_Lean_addMacroScope(v_quotContext_607_, v___x_619_, v_currMacroScope_608_);
v___x_621_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__7));
lean_inc_n(v___x_616_, 6);
v___x_622_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_622_, 0, v___x_616_);
lean_ctor_set(v___x_622_, 1, v___x_618_);
lean_ctor_set(v___x_622_, 2, v___x_620_);
lean_ctor_set(v___x_622_, 3, v___x_621_);
v___x_623_ = ((lean_object*)(l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__24));
v___x_624_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleEPost__1___closed__1));
v___x_625_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleEPost__1___closed__2));
v___x_626_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_626_, 0, v___x_616_);
lean_ctor_set(v___x_626_, 1, v___x_625_);
v___x_627_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__6, &l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__6_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__6);
v___x_628_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleEPost__1___closed__3));
v___x_629_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_Es_612_);
lean_dec_ref(v_Es_612_);
v___x_630_ = l_Lean_Syntax_SepArray_ofElems(v___x_628_, v___x_629_);
lean_dec_ref(v___x_629_);
v___x_631_ = l_Array_append___redArg(v___x_627_, v___x_630_);
lean_dec_ref(v___x_630_);
v___x_632_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_632_, 0, v___x_616_);
lean_ctor_set(v___x_632_, 1, v___x_623_);
lean_ctor_set(v___x_632_, 2, v___x_631_);
v___x_633_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleEPost__1___closed__4));
v___x_634_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_634_, 0, v___x_616_);
lean_ctor_set(v___x_634_, 1, v___x_633_);
v___x_635_ = l_Lean_Syntax_node3(v___x_616_, v___x_624_, v___x_626_, v___x_632_, v___x_634_);
v___x_636_ = l_Lean_Syntax_node4(v___x_616_, v___x_623_, v_a_602_, v___x_594_, v___x_614_, v___x_635_);
v___x_637_ = l_Lean_Syntax_node2(v___x_616_, v___x_617_, v___x_622_, v___x_636_);
if (v_isShared_606_ == 0)
{
lean_ctor_set(v___x_605_, 0, v___x_637_);
v___x_639_ = v___x_605_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v___x_637_);
lean_ctor_set(v_reuseFailAlloc_640_, 1, v_a_603_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
return v___x_639_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleEPost__1___boxed(lean_object* v_x_657_, lean_object* v_a_658_, lean_object* v_a_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleEPost__1(v_x_657_, v_a_658_, v_a_659_);
lean_dec_ref(v_a_658_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_unexpandTriple(lean_object* v_x_669_, lean_object* v_a_670_, lean_object* v_a_671_){
_start:
{
lean_object* v___x_672_; uint8_t v___x_673_; 
v___x_672_ = ((lean_object*)(l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__26));
lean_inc(v_x_669_);
v___x_673_ = l_Lean_Syntax_isOfKind(v_x_669_, v___x_672_);
if (v___x_673_ == 0)
{
lean_object* v___x_674_; lean_object* v___x_675_; 
lean_dec(v_x_669_);
v___x_674_ = lean_box(0);
v___x_675_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_675_, 0, v___x_674_);
lean_ctor_set(v___x_675_, 1, v_a_671_);
return v___x_675_;
}
else
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; uint8_t v___x_679_; 
v___x_676_ = lean_unsigned_to_nat(1u);
v___x_677_ = l_Lean_Syntax_getArg(v_x_669_, v___x_676_);
lean_dec(v_x_669_);
v___x_678_ = lean_unsigned_to_nat(4u);
lean_inc(v___x_677_);
v___x_679_ = l_Lean_Syntax_matchesNull(v___x_677_, v___x_678_);
if (v___x_679_ == 0)
{
lean_object* v___x_680_; lean_object* v___x_681_; 
lean_dec(v___x_677_);
v___x_680_ = lean_box(0);
v___x_681_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_681_, 0, v___x_680_);
lean_ctor_set(v___x_681_, 1, v_a_671_);
return v___x_681_;
}
else
{
lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; uint8_t v___x_690_; 
v___x_682_ = lean_unsigned_to_nat(0u);
v___x_683_ = l_Lean_Syntax_getArg(v___x_677_, v___x_682_);
v___x_684_ = l_Lean_Syntax_getArg(v___x_677_, v___x_676_);
v___x_685_ = lean_unsigned_to_nat(2u);
v___x_686_ = l_Lean_Syntax_getArg(v___x_677_, v___x_685_);
v___x_687_ = lean_unsigned_to_nat(3u);
v___x_688_ = l_Lean_Syntax_getArg(v___x_677_, v___x_687_);
lean_dec(v___x_677_);
v___x_689_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleEPost__1___closed__1));
lean_inc(v___x_688_);
v___x_690_ = l_Lean_Syntax_isOfKind(v___x_688_, v___x_689_);
if (v___x_690_ == 0)
{
lean_object* v___x_691_; uint8_t v___x_692_; 
v___x_691_ = ((lean_object*)(l_Std_Internal_Do_unexpandTriple___closed__1));
lean_inc(v___x_688_);
v___x_692_ = l_Lean_Syntax_isOfKind(v___x_688_, v___x_691_);
if (v___x_692_ == 0)
{
lean_object* v___x_693_; uint8_t v___x_694_; 
v___x_693_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleNotation__1___closed__11));
v___x_694_ = l_Lean_Syntax_matchesIdent(v___x_688_, v___x_693_);
lean_dec(v___x_688_);
if (v___x_694_ == 0)
{
lean_object* v___x_695_; lean_object* v___x_696_; 
lean_dec(v___x_686_);
lean_dec(v___x_684_);
lean_dec(v___x_683_);
v___x_695_ = lean_box(0);
v___x_696_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_696_, 0, v___x_695_);
lean_ctor_set(v___x_696_, 1, v_a_671_);
return v___x_696_;
}
else
{
lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_697_ = l_Lean_SourceInfo_fromRef(v_a_670_, v___x_692_);
v___x_698_ = ((lean_object*)(l_Std_Internal_Do_tripleNotation___closed__1));
v___x_699_ = ((lean_object*)(l_Std_Internal_Do_unexpandTriple___closed__2));
lean_inc_n(v___x_697_, 3);
v___x_700_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_700_, 0, v___x_697_);
lean_ctor_set(v___x_700_, 1, v___x_699_);
v___x_701_ = ((lean_object*)(l_Std_Internal_Do_unexpandTriple___closed__3));
v___x_702_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_702_, 0, v___x_697_);
lean_ctor_set(v___x_702_, 1, v___x_701_);
v___x_703_ = ((lean_object*)(l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__24));
v___x_704_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__6, &l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__6_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__6);
v___x_705_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_705_, 0, v___x_697_);
lean_ctor_set(v___x_705_, 1, v___x_703_);
lean_ctor_set(v___x_705_, 2, v___x_704_);
lean_inc_ref(v___x_702_);
lean_inc_ref(v___x_700_);
v___x_706_ = l_Lean_Syntax_node8(v___x_697_, v___x_698_, v___x_700_, v___x_684_, v___x_702_, v___x_705_, v___x_683_, v___x_700_, v___x_686_, v___x_702_);
v___x_707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_707_, 0, v___x_706_);
lean_ctor_set(v___x_707_, 1, v_a_671_);
return v___x_707_;
}
}
else
{
lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; 
lean_dec(v___x_688_);
v___x_708_ = l_Lean_SourceInfo_fromRef(v_a_670_, v___x_690_);
v___x_709_ = ((lean_object*)(l_Std_Internal_Do_tripleNotation___closed__1));
v___x_710_ = ((lean_object*)(l_Std_Internal_Do_unexpandTriple___closed__2));
lean_inc_n(v___x_708_, 3);
v___x_711_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_711_, 0, v___x_708_);
lean_ctor_set(v___x_711_, 1, v___x_710_);
v___x_712_ = ((lean_object*)(l_Std_Internal_Do_unexpandTriple___closed__3));
v___x_713_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_713_, 0, v___x_708_);
lean_ctor_set(v___x_713_, 1, v___x_712_);
v___x_714_ = ((lean_object*)(l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__24));
v___x_715_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__6, &l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__6_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__6);
v___x_716_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_716_, 0, v___x_708_);
lean_ctor_set(v___x_716_, 1, v___x_714_);
lean_ctor_set(v___x_716_, 2, v___x_715_);
lean_inc_ref(v___x_713_);
lean_inc_ref(v___x_711_);
v___x_717_ = l_Lean_Syntax_node8(v___x_708_, v___x_709_, v___x_711_, v___x_684_, v___x_713_, v___x_716_, v___x_683_, v___x_711_, v___x_686_, v___x_713_);
v___x_718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_718_, 0, v___x_717_);
lean_ctor_set(v___x_718_, 1, v_a_671_);
return v___x_718_;
}
}
else
{
lean_object* v___x_719_; lean_object* v_Es_720_; lean_object* v___x_721_; lean_object* v___x_722_; uint8_t v___x_723_; 
v___x_719_ = l_Lean_Syntax_getArg(v___x_688_, v___x_676_);
lean_dec(v___x_688_);
v_Es_720_ = l_Lean_Syntax_getArgs(v___x_719_);
lean_dec(v___x_719_);
v___x_721_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_Es_720_);
lean_dec_ref(v_Es_720_);
v___x_722_ = lean_array_get_size(v___x_721_);
v___x_723_ = lean_nat_dec_eq(v___x_722_, v___x_682_);
if (v___x_723_ == 0)
{
lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_724_ = l_Lean_SourceInfo_fromRef(v_a_670_, v___x_723_);
v___x_725_ = ((lean_object*)(l_Std_Internal_Do_tripleEPost___closed__1));
v___x_726_ = ((lean_object*)(l_Std_Internal_Do_unexpandTriple___closed__2));
lean_inc_n(v___x_724_, 5);
v___x_727_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_727_, 0, v___x_724_);
lean_ctor_set(v___x_727_, 1, v___x_726_);
v___x_728_ = ((lean_object*)(l_Std_Internal_Do_unexpandTriple___closed__3));
v___x_729_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_729_, 0, v___x_724_);
lean_ctor_set(v___x_729_, 1, v___x_728_);
v___x_730_ = ((lean_object*)(l___private_Std_Internal_Do_Triple_Basic_0__Std_Internal_Do_hintProgram___closed__24));
v___x_731_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__6, &l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__6_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleBinderNotation__1___closed__6);
v___x_732_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_732_, 0, v___x_724_);
lean_ctor_set(v___x_732_, 1, v___x_730_);
lean_ctor_set(v___x_732_, 2, v___x_731_);
v___x_733_ = ((lean_object*)(l_Std_Internal_Do_unexpandTriple___closed__4));
v___x_734_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_734_, 0, v___x_724_);
lean_ctor_set(v___x_734_, 1, v___x_733_);
v___x_735_ = l_Lean_Syntax_SepArray_ofElems(v___x_733_, v___x_721_);
lean_dec_ref(v___x_721_);
v___x_736_ = l_Array_append___redArg(v___x_731_, v___x_735_);
lean_dec_ref(v___x_735_);
v___x_737_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_737_, 0, v___x_724_);
lean_ctor_set(v___x_737_, 1, v___x_730_);
lean_ctor_set(v___x_737_, 2, v___x_736_);
v___x_738_ = lean_unsigned_to_nat(10u);
v___x_739_ = lean_mk_empty_array_with_capacity(v___x_738_);
lean_inc_ref(v___x_727_);
v___x_740_ = lean_array_push(v___x_739_, v___x_727_);
v___x_741_ = lean_array_push(v___x_740_, v___x_684_);
lean_inc_ref(v___x_729_);
v___x_742_ = lean_array_push(v___x_741_, v___x_729_);
v___x_743_ = lean_array_push(v___x_742_, v___x_732_);
v___x_744_ = lean_array_push(v___x_743_, v___x_683_);
v___x_745_ = lean_array_push(v___x_744_, v___x_727_);
v___x_746_ = lean_array_push(v___x_745_, v___x_686_);
v___x_747_ = lean_array_push(v___x_746_, v___x_734_);
v___x_748_ = lean_array_push(v___x_747_, v___x_737_);
v___x_749_ = lean_array_push(v___x_748_, v___x_729_);
v___x_750_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_750_, 0, v___x_724_);
lean_ctor_set(v___x_750_, 1, v___x_725_);
lean_ctor_set(v___x_750_, 2, v___x_749_);
v___x_751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_751_, 0, v___x_750_);
lean_ctor_set(v___x_751_, 1, v_a_671_);
return v___x_751_;
}
else
{
lean_object* v___x_752_; lean_object* v___x_753_; 
lean_dec_ref(v___x_721_);
lean_dec(v___x_686_);
lean_dec(v___x_684_);
lean_dec(v___x_683_);
v___x_752_ = lean_box(0);
v___x_753_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_753_, 0, v___x_752_);
lean_ctor_set(v___x_753_, 1, v_a_671_);
return v___x_753_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_unexpandTriple___boxed(lean_object* v_x_754_, lean_object* v_a_755_, lean_object* v_a_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l_Std_Internal_Do_unexpandTriple(v_x_754_, v_a_755_, v_a_756_);
lean_dec(v_a_755_);
return v_res_757_;
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

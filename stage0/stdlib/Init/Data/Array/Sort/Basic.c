// Lean compiler output
// Module: Init.Data.Array.Sort.Basic
// Imports: public import Init.Data.Array.Subarray.Split public import Init.Data.Slice.Array import Init.Omega
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
static const lean_string_object l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__3_value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__4_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__4_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__4_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__4_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static const lean_array_object l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__6_value;
static const lean_ctor_object l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__7_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__7_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__7_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__7_value;
static const lean_string_object l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__8_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__9_value;
static const lean_string_object l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__10_value;
static const lean_ctor_object l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__11_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__11_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__11_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__11 = (const lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__11_value;
lean_object* l_Lean_mkAtom(lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__12;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__13;
static const lean_string_object l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__14 = (const lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__14_value;
static const lean_string_object l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__15 = (const lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__15_value;
static const lean_ctor_object l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__16_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__16_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__16_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__16 = (const lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__16_value;
static const lean_string_object l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__17 = (const lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__17_value;
static const lean_ctor_object l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__18_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__18_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__18_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__17_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__18 = (const lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__18_value;
static const lean_string_object l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__19 = (const lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__19_value;
static lean_once_cell_t l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__20;
static lean_once_cell_t l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__21;
static const lean_string_object l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__22 = (const lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__22_value;
static const lean_ctor_object l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__23 = (const lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__23_value;
static const lean_string_object l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "[anonymous]"};
static const lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__24 = (const lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__24_value;
lean_object* lean_string_utf8_byte_size(lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__25;
static lean_once_cell_t l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__26;
static lean_once_cell_t l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__27;
static lean_once_cell_t l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__28;
static lean_once_cell_t l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__29;
static lean_once_cell_t l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__30;
static lean_once_cell_t l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__31;
static lean_once_cell_t l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__32;
static const lean_string_object l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 7, .m_data = "term_≤_"};
static const lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__33 = (const lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__33_value;
static const lean_ctor_object l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__33_value),LEAN_SCALAR_PTR_LITERAL(111, 3, 61, 112, 38, 138, 106, 121)}};
static const lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__34 = (const lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__34_value;
static const lean_string_object l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cdot"};
static const lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__35 = (const lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__35_value;
static const lean_ctor_object l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__36_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__36_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__36_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__36_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__36_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__36_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__35_value),LEAN_SCALAR_PTR_LITERAL(215, 94, 65, 66, 49, 100, 151, 85)}};
static const lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__36 = (const lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__36_value;
static const lean_string_object l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 1, .m_data = "·"};
static const lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__37 = (const lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__37_value;
static lean_once_cell_t l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__38;
static lean_once_cell_t l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__39;
static lean_once_cell_t l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__40;
static lean_once_cell_t l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__41;
static lean_once_cell_t l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__42;
static const lean_string_object l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "≤"};
static const lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__43 = (const lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__43_value;
static lean_once_cell_t l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__44;
static lean_once_cell_t l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__45;
static lean_once_cell_t l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__46_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__46;
static lean_once_cell_t l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__47_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__47;
static lean_once_cell_t l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__48_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__48;
static const lean_string_object l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__49 = (const lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__49_value;
static lean_once_cell_t l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__50_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__50;
static lean_once_cell_t l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__51_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__51;
static lean_once_cell_t l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__52_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__52;
static lean_once_cell_t l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__53_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__53;
static lean_once_cell_t l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__54_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__54;
static lean_once_cell_t l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__55_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__55;
static lean_once_cell_t l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__56_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__56;
static lean_once_cell_t l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__57_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__57;
static lean_once_cell_t l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__58_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__58;
static lean_once_cell_t l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__59_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__59;
static lean_once_cell_t l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__60_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__60;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge_go_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Subarray_get___redArg(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Subarray_drop___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_mergeSort___auto__1;
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Subarray_mergeSort_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static const lean_array_object l_Subarray_mergeSort___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Subarray_mergeSort___redArg___closed__0 = (const lean_object*)&l_Subarray_mergeSort___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Subarray_mergeSort___redArg(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_mergeSort(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Subarray_mergeSort_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mergeSort___auto__1;
LEAN_EXPORT lean_object* l_Array_mergeSort___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mergeSort(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__12(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__10));
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__13(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__12, &l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__12_once, _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__12);
x_2 = ((lean_object*)(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__5));
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__20(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__19));
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__21(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__20, &l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__20_once, _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__20);
x_2 = ((lean_object*)(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__5));
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__25(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__24));
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__26(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__25, &l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__25_once, _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__25);
x_2 = lean_unsigned_to_nat(0u);
x_3 = ((lean_object*)(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__24));
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__27(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_obj_once(&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__26, &l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__26_once, _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__26);
x_4 = lean_box(2);
x_5 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__28(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__27, &l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__27_once, _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__27);
x_2 = ((lean_object*)(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__5));
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__29(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__28, &l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__28_once, _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__28);
x_2 = ((lean_object*)(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__23));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__30(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__29, &l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__29_once, _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__29);
x_2 = lean_obj_once(&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__21, &l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__21_once, _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__21);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__31(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__30, &l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__30_once, _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__30);
x_2 = ((lean_object*)(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__18));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__32(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__31, &l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__31_once, _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__31);
x_2 = ((lean_object*)(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__5));
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__38(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__37));
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__39(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__38, &l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__38_once, _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__38);
x_2 = ((lean_object*)(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__5));
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__40(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__29, &l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__29_once, _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__29);
x_2 = lean_obj_once(&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__39, &l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__39_once, _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__39);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__41(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__40, &l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__40_once, _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__40);
x_2 = ((lean_object*)(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__36));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__42(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__41, &l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__41_once, _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__41);
x_2 = ((lean_object*)(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__5));
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__44(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__43));
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__45(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__44, &l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__44_once, _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__44);
x_2 = lean_obj_once(&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__42, &l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__42_once, _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__42);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__46(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__41, &l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__41_once, _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__41);
x_2 = lean_obj_once(&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__45, &l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__45_once, _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__45);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__47(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__46, &l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__46_once, _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__46);
x_2 = ((lean_object*)(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__34));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__48(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__47, &l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__47_once, _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__47);
x_2 = lean_obj_once(&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__32, &l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__32_once, _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__32);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__50(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__49));
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__51(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__50, &l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__50_once, _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__50);
x_2 = lean_obj_once(&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__48, &l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__48_once, _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__48);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__52(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__51, &l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__51_once, _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__51);
x_2 = ((lean_object*)(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__16));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__53(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__52, &l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__52_once, _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__52);
x_2 = lean_obj_once(&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__13, &l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__13_once, _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__13);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__54(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__53, &l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__53_once, _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__53);
x_2 = ((lean_object*)(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__11));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__55(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__54, &l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__54_once, _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__54);
x_2 = ((lean_object*)(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__5));
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__56(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__55, &l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__55_once, _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__55);
x_2 = ((lean_object*)(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__9));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__57(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__56, &l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__56_once, _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__56);
x_2 = ((lean_object*)(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__5));
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__58(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__57, &l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__57_once, _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__57);
x_2 = ((lean_object*)(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__7));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__59(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__58, &l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__58_once, _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__58);
x_2 = ((lean_object*)(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__5));
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__60(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__59, &l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__59_once, _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__59);
x_2 = ((lean_object*)(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__4));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__60, &l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__60_once, _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__60);
return x_1;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge_go_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_18; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_18 = !lean_is_exclusive(x_1);
if (x_18 == 0)
{
x_6 = x_1;
x_7 = x_18;
goto block_17;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = x_18;
goto block_17;
}
block_17:
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_4, x_5);
if (x_8 == 0)
{
lean_del_object(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_4, x_9);
lean_inc_ref(x_3);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_10);
x_11 = x_6;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_3);
lean_ctor_set(x_16, 1, x_10);
lean_ctor_set(x_16, 2, x_5);
x_11 = x_16;
goto block_15;
}
block_15:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_array_fget(x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
x_13 = lean_array_push(x_2, x_12);
x_1 = x_11;
x_2 = x_13;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge_go___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 2);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Subarray_get___redArg(x_2, x_9);
x_11 = l_Subarray_get___redArg(x_3, x_9);
lean_inc_ref(x_1);
lean_inc(x_11);
lean_inc(x_10);
x_12 = lean_apply_2(x_1, x_10, x_11);
x_13 = lean_unbox(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_dec(x_10);
x_14 = lean_nat_sub(x_8, x_7);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_dec_lt(x_15, x_14);
lean_dec(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_17 = lean_array_push(x_4, x_11);
x_18 = l_WellFounded_opaqueFix_u2083___at___00__private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge_go_spec__0___redArg(x_2, x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = l_Subarray_drop___redArg(x_3, x_15);
x_20 = lean_array_push(x_4, x_11);
x_3 = x_19;
x_4 = x_20;
goto _start;
}
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_dec(x_11);
x_22 = lean_nat_sub(x_6, x_5);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_dec_lt(x_23, x_22);
lean_dec(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_25 = lean_array_push(x_4, x_10);
x_26 = l_WellFounded_opaqueFix_u2083___at___00__private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge_go_spec__0___redArg(x_3, x_25);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = l_Subarray_drop___redArg(x_2, x_23);
x_28 = lean_array_push(x_4, x_10);
x_2 = x_27;
x_4 = x_28;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge_go___redArg(x_2, x_3, x_4, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge_go_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_WellFounded_opaqueFix_u2083___at___00__private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge_go_spec__0___redArg(x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_4, x_5);
if (x_6 == 0)
{
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_2;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_4, x_7);
if (x_8 == 0)
{
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_1;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = l_Array_toSubarray___redArg(x_1, x_4, x_5);
x_10 = l_Array_toSubarray___redArg(x_2, x_4, x_7);
x_11 = lean_nat_add(x_5, x_7);
x_12 = lean_mk_empty_array_with_capacity(x_11);
lean_dec(x_11);
x_13 = l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge_go___redArg(x_3, x_9, x_10, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___redArg(x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Subarray_mergeSort___auto__1(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__60, &l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__60_once, _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__60);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Subarray_mergeSort_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_18; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_18 = !lean_is_exclusive(x_1);
if (x_18 == 0)
{
x_6 = x_1;
x_7 = x_18;
goto block_17;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = x_18;
goto block_17;
}
block_17:
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_4, x_5);
if (x_8 == 0)
{
lean_del_object(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_4, x_9);
lean_inc_ref(x_3);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_10);
x_11 = x_6;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_3);
lean_ctor_set(x_16, 1, x_10);
lean_ctor_set(x_16, 2, x_5);
x_11 = x_16;
goto block_15;
}
block_15:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_array_fget(x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
x_13 = lean_array_push(x_2, x_12);
x_1 = x_11;
x_2 = x_13;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_mergeSort___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_5, x_4);
x_18 = lean_nat_dec_lt(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_17);
lean_dec_ref(x_2);
x_19 = ((lean_object*)(l_Subarray_mergeSort___redArg___closed__0));
x_20 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Subarray_mergeSort_spec__0___redArg(x_1, x_19);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_31; uint8_t x_32; 
lean_inc(x_4);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_21 = lean_nat_add(x_17, x_16);
x_22 = lean_nat_shiftr(x_21, x_16);
lean_dec(x_21);
x_31 = lean_unsigned_to_nat(0u);
x_32 = lean_nat_dec_le(x_22, x_17);
if (x_32 == 0)
{
lean_inc(x_17);
x_23 = x_31;
x_24 = x_17;
goto block_30;
}
else
{
lean_inc(x_22);
x_23 = x_31;
x_24 = x_22;
goto block_30;
}
block_30:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_25 = lean_nat_add(x_23, x_4);
x_26 = lean_nat_add(x_24, x_4);
lean_dec(x_24);
lean_inc_ref(x_3);
x_27 = l_Array_toSubarray___redArg(x_3, x_25, x_26);
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_nat_dec_le(x_22, x_28);
if (x_29 == 0)
{
x_6 = x_27;
x_7 = x_22;
x_8 = x_17;
goto block_15;
}
else
{
lean_dec(x_22);
x_6 = x_27;
x_7 = x_28;
x_8 = x_17;
goto block_15;
}
}
}
block_15:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_nat_add(x_7, x_4);
lean_dec(x_7);
x_10 = lean_nat_add(x_8, x_4);
lean_dec(x_4);
lean_dec(x_8);
x_11 = l_Array_toSubarray___redArg(x_3, x_9, x_10);
lean_inc_ref(x_2);
x_12 = l_Subarray_mergeSort___redArg(x_6, x_2);
lean_inc_ref(x_2);
x_13 = l_Subarray_mergeSort___redArg(x_11, x_2);
x_14 = l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___redArg(x_12, x_13, x_2);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Subarray_mergeSort(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Subarray_mergeSort___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Subarray_mergeSort_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Subarray_mergeSort_spec__0___redArg(x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Array_mergeSort___auto__1(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__60, &l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__60_once, _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__60);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mergeSort___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_1);
x_5 = l_Array_toSubarray___redArg(x_1, x_3, x_4);
x_6 = l_Subarray_mergeSort___redArg(x_5, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mergeSort(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_array_get_size(x_2);
x_6 = l_Array_toSubarray___redArg(x_2, x_4, x_5);
x_7 = l_Subarray_mergeSort___redArg(x_6, x_3);
return x_7;
}
}
lean_object* runtime_initialize_Init_Data_Array_Subarray_Split(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Slice_Array(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Array_Sort_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Array_Subarray_Split(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Slice_Array(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Array_Sort_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1 = _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1();
lean_mark_persistent(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1);
l_Subarray_mergeSort___auto__1 = _init_l_Subarray_mergeSort___auto__1();
lean_mark_persistent(l_Subarray_mergeSort___auto__1);
l_Array_mergeSort___auto__1 = _init_l_Array_mergeSort___auto__1();
lean_mark_persistent(l_Array_mergeSort___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Array_Subarray_Split(uint8_t builtin);
lean_object* initialize_Init_Data_Slice_Array(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Array_Sort_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Array_Subarray_Split(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Slice_Array(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Sort_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Array_Sort_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Array_Sort_Basic(builtin);
}
#ifdef __cplusplus
}
#endif

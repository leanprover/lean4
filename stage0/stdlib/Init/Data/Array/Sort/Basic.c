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
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Subarray_get___redArg(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Subarray_drop___redArg(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__4_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__4_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__4_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__4_value;
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
static const lean_ctor_object l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__9_value;
static const lean_string_object l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__10_value;
static const lean_ctor_object l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__11_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__11_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__11_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__11 = (const lean_object*)&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__11_value;
static lean_once_cell_t l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__12;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge_go_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_mergeSort___auto__1;
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Subarray_mergeSort_spec__0___redArg(lean_object*, lean_object*);
static const lean_array_object l_Subarray_mergeSort___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Subarray_mergeSort___redArg___closed__0 = (const lean_object*)&l_Subarray_mergeSort___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Subarray_mergeSort___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_mergeSort(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Subarray_mergeSort_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mergeSort___auto__1;
LEAN_EXPORT lean_object* l_Array_mergeSort___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mergeSort(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__12(void){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_27_ = ((lean_object*)(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__10));
v___x_28_ = l_Lean_mkAtom(v___x_27_);
return v___x_28_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__13(void){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_29_ = lean_obj_once(&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__12, &l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__12_once, _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__12);
v___x_30_ = ((lean_object*)(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__5));
v___x_31_ = lean_array_push(v___x_30_, v___x_29_);
return v___x_31_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__20(void){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_46_ = ((lean_object*)(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__19));
v___x_47_ = l_Lean_mkAtom(v___x_46_);
return v___x_47_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__21(void){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_48_ = lean_obj_once(&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__20, &l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__20_once, _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__20);
v___x_49_ = ((lean_object*)(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__5));
v___x_50_ = lean_array_push(v___x_49_, v___x_48_);
return v___x_50_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__25(void){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_55_ = ((lean_object*)(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__24));
v___x_56_ = lean_string_utf8_byte_size(v___x_55_);
return v___x_56_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__26(void){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_57_ = lean_obj_once(&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__25, &l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__25_once, _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__25);
v___x_58_ = lean_unsigned_to_nat(0u);
v___x_59_ = ((lean_object*)(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__24));
v___x_60_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_60_, 0, v___x_59_);
lean_ctor_set(v___x_60_, 1, v___x_58_);
lean_ctor_set(v___x_60_, 2, v___x_57_);
return v___x_60_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__27(void){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_61_ = lean_box(0);
v___x_62_ = lean_box(0);
v___x_63_ = lean_obj_once(&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__26, &l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__26_once, _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__26);
v___x_64_ = lean_box(2);
v___x_65_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_65_, 0, v___x_64_);
lean_ctor_set(v___x_65_, 1, v___x_63_);
lean_ctor_set(v___x_65_, 2, v___x_62_);
lean_ctor_set(v___x_65_, 3, v___x_61_);
return v___x_65_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__28(void){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_66_ = lean_obj_once(&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__27, &l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__27_once, _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__27);
v___x_67_ = ((lean_object*)(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__5));
v___x_68_ = lean_array_push(v___x_67_, v___x_66_);
return v___x_68_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__29(void){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_69_ = lean_obj_once(&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__28, &l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__28_once, _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__28);
v___x_70_ = ((lean_object*)(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__23));
v___x_71_ = lean_box(2);
v___x_72_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_72_, 0, v___x_71_);
lean_ctor_set(v___x_72_, 1, v___x_70_);
lean_ctor_set(v___x_72_, 2, v___x_69_);
return v___x_72_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__30(void){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_73_ = lean_obj_once(&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__29, &l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__29_once, _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__29);
v___x_74_ = lean_obj_once(&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__21, &l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__21_once, _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__21);
v___x_75_ = lean_array_push(v___x_74_, v___x_73_);
return v___x_75_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__31(void){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_76_ = lean_obj_once(&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__30, &l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__30_once, _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__30);
v___x_77_ = ((lean_object*)(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__18));
v___x_78_ = lean_box(2);
v___x_79_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_79_, 0, v___x_78_);
lean_ctor_set(v___x_79_, 1, v___x_77_);
lean_ctor_set(v___x_79_, 2, v___x_76_);
return v___x_79_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__32(void){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_80_ = lean_obj_once(&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__31, &l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__31_once, _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__31);
v___x_81_ = ((lean_object*)(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__5));
v___x_82_ = lean_array_push(v___x_81_, v___x_80_);
return v___x_82_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__38(void){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_93_ = ((lean_object*)(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__37));
v___x_94_ = l_Lean_mkAtom(v___x_93_);
return v___x_94_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__39(void){
_start:
{
lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_95_ = lean_obj_once(&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__38, &l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__38_once, _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__38);
v___x_96_ = ((lean_object*)(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__5));
v___x_97_ = lean_array_push(v___x_96_, v___x_95_);
return v___x_97_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__40(void){
_start:
{
lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_98_ = lean_obj_once(&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__29, &l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__29_once, _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__29);
v___x_99_ = lean_obj_once(&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__39, &l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__39_once, _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__39);
v___x_100_ = lean_array_push(v___x_99_, v___x_98_);
return v___x_100_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__41(void){
_start:
{
lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_101_ = lean_obj_once(&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__40, &l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__40_once, _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__40);
v___x_102_ = ((lean_object*)(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__36));
v___x_103_ = lean_box(2);
v___x_104_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_104_, 0, v___x_103_);
lean_ctor_set(v___x_104_, 1, v___x_102_);
lean_ctor_set(v___x_104_, 2, v___x_101_);
return v___x_104_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__42(void){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_105_ = lean_obj_once(&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__41, &l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__41_once, _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__41);
v___x_106_ = ((lean_object*)(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__5));
v___x_107_ = lean_array_push(v___x_106_, v___x_105_);
return v___x_107_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__44(void){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_109_ = ((lean_object*)(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__43));
v___x_110_ = l_Lean_mkAtom(v___x_109_);
return v___x_110_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__45(void){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_111_ = lean_obj_once(&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__44, &l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__44_once, _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__44);
v___x_112_ = lean_obj_once(&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__42, &l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__42_once, _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__42);
v___x_113_ = lean_array_push(v___x_112_, v___x_111_);
return v___x_113_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__46(void){
_start:
{
lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_114_ = lean_obj_once(&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__41, &l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__41_once, _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__41);
v___x_115_ = lean_obj_once(&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__45, &l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__45_once, _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__45);
v___x_116_ = lean_array_push(v___x_115_, v___x_114_);
return v___x_116_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__47(void){
_start:
{
lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_117_ = lean_obj_once(&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__46, &l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__46_once, _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__46);
v___x_118_ = ((lean_object*)(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__34));
v___x_119_ = lean_box(2);
v___x_120_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_120_, 0, v___x_119_);
lean_ctor_set(v___x_120_, 1, v___x_118_);
lean_ctor_set(v___x_120_, 2, v___x_117_);
return v___x_120_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__48(void){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_121_ = lean_obj_once(&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__47, &l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__47_once, _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__47);
v___x_122_ = lean_obj_once(&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__32, &l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__32_once, _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__32);
v___x_123_ = lean_array_push(v___x_122_, v___x_121_);
return v___x_123_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__50(void){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_125_ = ((lean_object*)(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__49));
v___x_126_ = l_Lean_mkAtom(v___x_125_);
return v___x_126_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__51(void){
_start:
{
lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_127_ = lean_obj_once(&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__50, &l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__50_once, _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__50);
v___x_128_ = lean_obj_once(&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__48, &l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__48_once, _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__48);
v___x_129_ = lean_array_push(v___x_128_, v___x_127_);
return v___x_129_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__52(void){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_130_ = lean_obj_once(&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__51, &l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__51_once, _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__51);
v___x_131_ = ((lean_object*)(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__16));
v___x_132_ = lean_box(2);
v___x_133_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_133_, 0, v___x_132_);
lean_ctor_set(v___x_133_, 1, v___x_131_);
lean_ctor_set(v___x_133_, 2, v___x_130_);
return v___x_133_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__53(void){
_start:
{
lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_134_ = lean_obj_once(&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__52, &l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__52_once, _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__52);
v___x_135_ = lean_obj_once(&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__13, &l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__13_once, _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__13);
v___x_136_ = lean_array_push(v___x_135_, v___x_134_);
return v___x_136_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__54(void){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_137_ = lean_obj_once(&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__53, &l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__53_once, _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__53);
v___x_138_ = ((lean_object*)(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__11));
v___x_139_ = lean_box(2);
v___x_140_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_140_, 0, v___x_139_);
lean_ctor_set(v___x_140_, 1, v___x_138_);
lean_ctor_set(v___x_140_, 2, v___x_137_);
return v___x_140_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__55(void){
_start:
{
lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_141_ = lean_obj_once(&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__54, &l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__54_once, _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__54);
v___x_142_ = ((lean_object*)(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__5));
v___x_143_ = lean_array_push(v___x_142_, v___x_141_);
return v___x_143_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__56(void){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_144_ = lean_obj_once(&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__55, &l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__55_once, _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__55);
v___x_145_ = ((lean_object*)(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__9));
v___x_146_ = lean_box(2);
v___x_147_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_147_, 0, v___x_146_);
lean_ctor_set(v___x_147_, 1, v___x_145_);
lean_ctor_set(v___x_147_, 2, v___x_144_);
return v___x_147_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__57(void){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_148_ = lean_obj_once(&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__56, &l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__56_once, _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__56);
v___x_149_ = ((lean_object*)(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__5));
v___x_150_ = lean_array_push(v___x_149_, v___x_148_);
return v___x_150_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__58(void){
_start:
{
lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_151_ = lean_obj_once(&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__57, &l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__57_once, _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__57);
v___x_152_ = ((lean_object*)(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__7));
v___x_153_ = lean_box(2);
v___x_154_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_154_, 0, v___x_153_);
lean_ctor_set(v___x_154_, 1, v___x_152_);
lean_ctor_set(v___x_154_, 2, v___x_151_);
return v___x_154_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__59(void){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_155_ = lean_obj_once(&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__58, &l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__58_once, _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__58);
v___x_156_ = ((lean_object*)(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__5));
v___x_157_ = lean_array_push(v___x_156_, v___x_155_);
return v___x_157_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__60(void){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_158_ = lean_obj_once(&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__59, &l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__59_once, _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__59);
v___x_159_ = ((lean_object*)(l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__4));
v___x_160_ = lean_box(2);
v___x_161_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_161_, 0, v___x_160_);
lean_ctor_set(v___x_161_, 1, v___x_159_);
lean_ctor_set(v___x_161_, 2, v___x_158_);
return v___x_161_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1(void){
_start:
{
lean_object* v___x_162_; 
v___x_162_ = lean_obj_once(&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__60, &l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__60_once, _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__60);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge_go_spec__0___redArg(lean_object* v_a_163_, lean_object* v_b_164_){
_start:
{
lean_object* v_array_165_; lean_object* v_start_166_; lean_object* v_stop_167_; lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_180_; 
v_array_165_ = lean_ctor_get(v_a_163_, 0);
v_start_166_ = lean_ctor_get(v_a_163_, 1);
v_stop_167_ = lean_ctor_get(v_a_163_, 2);
v_isSharedCheck_180_ = !lean_is_exclusive(v_a_163_);
if (v_isSharedCheck_180_ == 0)
{
v___x_169_ = v_a_163_;
v_isShared_170_ = v_isSharedCheck_180_;
goto v_resetjp_168_;
}
else
{
lean_inc(v_stop_167_);
lean_inc(v_start_166_);
lean_inc(v_array_165_);
lean_dec(v_a_163_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_180_;
goto v_resetjp_168_;
}
v_resetjp_168_:
{
uint8_t v___x_171_; 
v___x_171_ = lean_nat_dec_lt(v_start_166_, v_stop_167_);
if (v___x_171_ == 0)
{
lean_del_object(v___x_169_);
lean_dec(v_stop_167_);
lean_dec(v_start_166_);
lean_dec_ref(v_array_165_);
return v_b_164_;
}
else
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_175_; 
v___x_172_ = lean_unsigned_to_nat(1u);
v___x_173_ = lean_nat_add(v_start_166_, v___x_172_);
lean_inc_ref(v_array_165_);
if (v_isShared_170_ == 0)
{
lean_ctor_set(v___x_169_, 1, v___x_173_);
v___x_175_ = v___x_169_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v_array_165_);
lean_ctor_set(v_reuseFailAlloc_179_, 1, v___x_173_);
lean_ctor_set(v_reuseFailAlloc_179_, 2, v_stop_167_);
v___x_175_ = v_reuseFailAlloc_179_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_176_ = lean_array_fget(v_array_165_, v_start_166_);
lean_dec(v_start_166_);
lean_dec_ref(v_array_165_);
v___x_177_ = lean_array_push(v_b_164_, v___x_176_);
v_a_163_ = v___x_175_;
v_b_164_ = v___x_177_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge_go___redArg(lean_object* v_le_181_, lean_object* v_xs_182_, lean_object* v_ys_183_, lean_object* v_acc_184_){
_start:
{
lean_object* v_start_185_; lean_object* v_stop_186_; lean_object* v_start_187_; lean_object* v_stop_188_; lean_object* v___x_189_; lean_object* v_x_190_; lean_object* v_y_191_; lean_object* v___x_192_; uint8_t v___x_193_; 
v_start_185_ = lean_ctor_get(v_xs_182_, 1);
v_stop_186_ = lean_ctor_get(v_xs_182_, 2);
v_start_187_ = lean_ctor_get(v_ys_183_, 1);
v_stop_188_ = lean_ctor_get(v_ys_183_, 2);
v___x_189_ = lean_unsigned_to_nat(0u);
v_x_190_ = l_Subarray_get___redArg(v_xs_182_, v___x_189_);
v_y_191_ = l_Subarray_get___redArg(v_ys_183_, v___x_189_);
lean_inc_ref(v_le_181_);
lean_inc(v_y_191_);
lean_inc(v_x_190_);
v___x_192_ = lean_apply_2(v_le_181_, v_x_190_, v_y_191_);
v___x_193_ = lean_unbox(v___x_192_);
if (v___x_193_ == 0)
{
lean_object* v___x_194_; lean_object* v___x_195_; uint8_t v___x_196_; 
lean_dec(v_x_190_);
v___x_194_ = lean_nat_sub(v_stop_188_, v_start_187_);
v___x_195_ = lean_unsigned_to_nat(1u);
v___x_196_ = lean_nat_dec_lt(v___x_195_, v___x_194_);
lean_dec(v___x_194_);
if (v___x_196_ == 0)
{
lean_object* v___x_197_; lean_object* v___x_198_; 
lean_dec_ref(v_ys_183_);
lean_dec_ref(v_le_181_);
v___x_197_ = lean_array_push(v_acc_184_, v_y_191_);
v___x_198_ = l_WellFounded_opaqueFix_u2083___at___00__private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge_go_spec__0___redArg(v_xs_182_, v___x_197_);
return v___x_198_;
}
else
{
lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_199_ = l_Subarray_drop___redArg(v_ys_183_, v___x_195_);
v___x_200_ = lean_array_push(v_acc_184_, v_y_191_);
v_ys_183_ = v___x_199_;
v_acc_184_ = v___x_200_;
goto _start;
}
}
else
{
lean_object* v___x_202_; lean_object* v___x_203_; uint8_t v___x_204_; 
lean_dec(v_y_191_);
v___x_202_ = lean_nat_sub(v_stop_186_, v_start_185_);
v___x_203_ = lean_unsigned_to_nat(1u);
v___x_204_ = lean_nat_dec_lt(v___x_203_, v___x_202_);
lean_dec(v___x_202_);
if (v___x_204_ == 0)
{
lean_object* v___x_205_; lean_object* v___x_206_; 
lean_dec_ref(v_xs_182_);
lean_dec_ref(v_le_181_);
v___x_205_ = lean_array_push(v_acc_184_, v_x_190_);
v___x_206_ = l_WellFounded_opaqueFix_u2083___at___00__private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge_go_spec__0___redArg(v_ys_183_, v___x_205_);
return v___x_206_;
}
else
{
lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_207_ = l_Subarray_drop___redArg(v_xs_182_, v___x_203_);
v___x_208_ = lean_array_push(v_acc_184_, v_x_190_);
v_xs_182_ = v___x_207_;
v_acc_184_ = v___x_208_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge_go(lean_object* v_00_u03b1_210_, lean_object* v_le_211_, lean_object* v_xs_212_, lean_object* v_ys_213_, lean_object* v_hxs_214_, lean_object* v_hys_215_, lean_object* v_acc_216_){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge_go___redArg(v_le_211_, v_xs_212_, v_ys_213_, v_acc_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge_go_spec__0(lean_object* v_00_u03b1_218_, lean_object* v_inst_219_, lean_object* v_R_220_, lean_object* v_a_221_, lean_object* v_b_222_, lean_object* v_c_223_){
_start:
{
lean_object* v___x_224_; 
v___x_224_ = l_WellFounded_opaqueFix_u2083___at___00__private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge_go_spec__0___redArg(v_a_221_, v_b_222_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___redArg(lean_object* v_xs_225_, lean_object* v_ys_226_, lean_object* v_le_227_){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; uint8_t v___x_230_; 
v___x_228_ = lean_unsigned_to_nat(0u);
v___x_229_ = lean_array_get_size(v_xs_225_);
v___x_230_ = lean_nat_dec_lt(v___x_228_, v___x_229_);
if (v___x_230_ == 0)
{
lean_dec_ref(v_le_227_);
lean_dec_ref(v_xs_225_);
return v_ys_226_;
}
else
{
lean_object* v___x_231_; uint8_t v___x_232_; 
v___x_231_ = lean_array_get_size(v_ys_226_);
v___x_232_ = lean_nat_dec_lt(v___x_228_, v___x_231_);
if (v___x_232_ == 0)
{
lean_dec_ref(v_le_227_);
lean_dec_ref(v_ys_226_);
return v_xs_225_;
}
else
{
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_233_ = l_Array_toSubarray___redArg(v_xs_225_, v___x_228_, v___x_229_);
v___x_234_ = l_Array_toSubarray___redArg(v_ys_226_, v___x_228_, v___x_231_);
v___x_235_ = lean_nat_add(v___x_229_, v___x_231_);
v___x_236_ = lean_mk_empty_array_with_capacity(v___x_235_);
lean_dec(v___x_235_);
v___x_237_ = l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge_go___redArg(v_le_227_, v___x_233_, v___x_234_, v___x_236_);
return v___x_237_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge(lean_object* v_00_u03b1_238_, lean_object* v_xs_239_, lean_object* v_ys_240_, lean_object* v_le_241_){
_start:
{
lean_object* v___x_242_; 
v___x_242_ = l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___redArg(v_xs_239_, v_ys_240_, v_le_241_);
return v___x_242_;
}
}
static lean_object* _init_l_Subarray_mergeSort___auto__1(void){
_start:
{
lean_object* v___x_243_; 
v___x_243_ = lean_obj_once(&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__60, &l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__60_once, _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__60);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Subarray_mergeSort_spec__0___redArg(lean_object* v_a_244_, lean_object* v_b_245_){
_start:
{
lean_object* v_array_246_; lean_object* v_start_247_; lean_object* v_stop_248_; lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_261_; 
v_array_246_ = lean_ctor_get(v_a_244_, 0);
v_start_247_ = lean_ctor_get(v_a_244_, 1);
v_stop_248_ = lean_ctor_get(v_a_244_, 2);
v_isSharedCheck_261_ = !lean_is_exclusive(v_a_244_);
if (v_isSharedCheck_261_ == 0)
{
v___x_250_ = v_a_244_;
v_isShared_251_ = v_isSharedCheck_261_;
goto v_resetjp_249_;
}
else
{
lean_inc(v_stop_248_);
lean_inc(v_start_247_);
lean_inc(v_array_246_);
lean_dec(v_a_244_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_261_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
uint8_t v___x_252_; 
v___x_252_ = lean_nat_dec_lt(v_start_247_, v_stop_248_);
if (v___x_252_ == 0)
{
lean_del_object(v___x_250_);
lean_dec(v_stop_248_);
lean_dec(v_start_247_);
lean_dec_ref(v_array_246_);
return v_b_245_;
}
else
{
lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_256_; 
v___x_253_ = lean_unsigned_to_nat(1u);
v___x_254_ = lean_nat_add(v_start_247_, v___x_253_);
lean_inc_ref(v_array_246_);
if (v_isShared_251_ == 0)
{
lean_ctor_set(v___x_250_, 1, v___x_254_);
v___x_256_ = v___x_250_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v_array_246_);
lean_ctor_set(v_reuseFailAlloc_260_, 1, v___x_254_);
lean_ctor_set(v_reuseFailAlloc_260_, 2, v_stop_248_);
v___x_256_ = v_reuseFailAlloc_260_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_257_ = lean_array_fget(v_array_246_, v_start_247_);
lean_dec(v_start_247_);
lean_dec_ref(v_array_246_);
v___x_258_ = lean_array_push(v_b_245_, v___x_257_);
v_a_244_ = v___x_256_;
v_b_245_ = v___x_258_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_mergeSort___redArg(lean_object* v_xs_264_, lean_object* v_le_265_){
_start:
{
lean_object* v_array_266_; lean_object* v_start_267_; lean_object* v_stop_268_; lean_object* v___y_270_; lean_object* v_lower_271_; lean_object* v_upper_272_; lean_object* v___x_279_; lean_object* v___x_280_; uint8_t v___x_281_; 
v_array_266_ = lean_ctor_get(v_xs_264_, 0);
v_start_267_ = lean_ctor_get(v_xs_264_, 1);
v_stop_268_ = lean_ctor_get(v_xs_264_, 2);
v___x_279_ = lean_unsigned_to_nat(1u);
v___x_280_ = lean_nat_sub(v_stop_268_, v_start_267_);
v___x_281_ = lean_nat_dec_lt(v___x_279_, v___x_280_);
if (v___x_281_ == 0)
{
lean_object* v___x_282_; lean_object* v___x_283_; 
lean_dec(v___x_280_);
lean_dec_ref(v_le_265_);
v___x_282_ = ((lean_object*)(l_Subarray_mergeSort___redArg___closed__0));
v___x_283_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Subarray_mergeSort_spec__0___redArg(v_xs_264_, v___x_282_);
return v___x_283_;
}
else
{
lean_object* v___x_284_; lean_object* v_splitIdx_285_; lean_object* v_lower_287_; lean_object* v_upper_288_; lean_object* v___x_294_; uint8_t v___x_295_; 
lean_inc(v_start_267_);
lean_inc_ref(v_array_266_);
lean_dec_ref(v_xs_264_);
v___x_284_ = lean_nat_add(v___x_280_, v___x_279_);
v_splitIdx_285_ = lean_nat_shiftr(v___x_284_, v___x_279_);
lean_dec(v___x_284_);
v___x_294_ = lean_unsigned_to_nat(0u);
v___x_295_ = lean_nat_dec_le(v_splitIdx_285_, v___x_280_);
if (v___x_295_ == 0)
{
lean_inc(v___x_280_);
v_lower_287_ = v___x_294_;
v_upper_288_ = v___x_280_;
goto v___jp_286_;
}
else
{
lean_inc(v_splitIdx_285_);
v_lower_287_ = v___x_294_;
v_upper_288_ = v_splitIdx_285_;
goto v___jp_286_;
}
v___jp_286_:
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; uint8_t v___x_293_; 
v___x_289_ = lean_nat_add(v_lower_287_, v_start_267_);
v___x_290_ = lean_nat_add(v_upper_288_, v_start_267_);
lean_dec(v_upper_288_);
lean_inc_ref(v_array_266_);
v___x_291_ = l_Array_toSubarray___redArg(v_array_266_, v___x_289_, v___x_290_);
v___x_292_ = lean_unsigned_to_nat(0u);
v___x_293_ = lean_nat_dec_le(v_splitIdx_285_, v___x_292_);
if (v___x_293_ == 0)
{
v___y_270_ = v___x_291_;
v_lower_271_ = v_splitIdx_285_;
v_upper_272_ = v___x_280_;
goto v___jp_269_;
}
else
{
lean_dec(v_splitIdx_285_);
v___y_270_ = v___x_291_;
v_lower_271_ = v___x_292_;
v_upper_272_ = v___x_280_;
goto v___jp_269_;
}
}
}
v___jp_269_:
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_273_ = lean_nat_add(v_lower_271_, v_start_267_);
lean_dec(v_lower_271_);
v___x_274_ = lean_nat_add(v_upper_272_, v_start_267_);
lean_dec(v_start_267_);
lean_dec(v_upper_272_);
v___x_275_ = l_Array_toSubarray___redArg(v_array_266_, v___x_273_, v___x_274_);
lean_inc_ref(v_le_265_);
v___x_276_ = l_Subarray_mergeSort___redArg(v___y_270_, v_le_265_);
lean_inc_ref(v_le_265_);
v___x_277_ = l_Subarray_mergeSort___redArg(v___x_275_, v_le_265_);
v___x_278_ = l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___redArg(v___x_276_, v___x_277_, v_le_265_);
return v___x_278_;
}
}
}
LEAN_EXPORT lean_object* l_Subarray_mergeSort(lean_object* v_00_u03b1_296_, lean_object* v_xs_297_, lean_object* v_le_298_){
_start:
{
lean_object* v___x_299_; 
v___x_299_ = l_Subarray_mergeSort___redArg(v_xs_297_, v_le_298_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Subarray_mergeSort_spec__0(lean_object* v_00_u03b1_300_, lean_object* v_inst_301_, lean_object* v_R_302_, lean_object* v_a_303_, lean_object* v_b_304_){
_start:
{
lean_object* v___x_305_; 
v___x_305_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Subarray_mergeSort_spec__0___redArg(v_a_303_, v_b_304_);
return v___x_305_;
}
}
static lean_object* _init_l_Array_mergeSort___auto__1(void){
_start:
{
lean_object* v___x_306_; 
v___x_306_ = lean_obj_once(&l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__60, &l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__60_once, _init_l___private_Init_Data_Array_Sort_Basic_0__Array_MergeSort_Internal_merge___auto__1___closed__60);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l_Array_mergeSort___redArg(lean_object* v_xs_307_, lean_object* v_le_308_){
_start:
{
lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_309_ = lean_unsigned_to_nat(0u);
v___x_310_ = lean_array_get_size(v_xs_307_);
v___x_311_ = l_Array_toSubarray___redArg(v_xs_307_, v___x_309_, v___x_310_);
v___x_312_ = l_Subarray_mergeSort___redArg(v___x_311_, v_le_308_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_Array_mergeSort(lean_object* v_00_u03b1_313_, lean_object* v_xs_314_, lean_object* v_le_315_){
_start:
{
lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_316_ = lean_unsigned_to_nat(0u);
v___x_317_ = lean_array_get_size(v_xs_314_);
v___x_318_ = l_Array_toSubarray___redArg(v_xs_314_, v___x_316_, v___x_317_);
v___x_319_ = l_Subarray_mergeSort___redArg(v___x_318_, v_le_315_);
return v___x_319_;
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
res = runtime_initialize_Init_Data_Array_Subarray_Split(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Slice_Array(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
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
res = initialize_Init_Data_Array_Subarray_Split(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Slice_Array(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Sort_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Array_Sort_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Array_Sort_Basic(builtin);
}
#ifdef __cplusplus
}
#endif

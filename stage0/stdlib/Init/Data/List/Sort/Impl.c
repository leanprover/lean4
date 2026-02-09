// Lean compiler output
// Module: Init.Data.List.Sort.Impl
// Imports: import all Init.Data.List.Sort.Basic public import Init.Data.List.Sort.Basic import Init.Data.List.Sort.Lemmas import Init.Data.Nat.Linear
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
lean_object* l_List_reverseAux___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeTR_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeTR_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeTR_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeTR_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_mergeTR___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_mergeTR(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_merge_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_merge_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_splitRevAt_go___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_splitRevAt_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_splitRevAt___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_splitRevAt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_splitRevAt_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_splitRevAt_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__0 = (const lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__0_value;
static const lean_string_object l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__1 = (const lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__1_value;
static const lean_string_object l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__2 = (const lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__2_value;
static const lean_string_object l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__3 = (const lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__3_value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__4_value_aux_0),((lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__4_value_aux_1),((lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__4_value_aux_2),((lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__4 = (const lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__4_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__5;
static const lean_string_object l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__6 = (const lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__6_value;
static const lean_ctor_object l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__7_value_aux_0),((lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__7_value_aux_1),((lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__7_value_aux_2),((lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__7 = (const lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__7_value;
static const lean_string_object l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__8 = (const lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__8_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__9 = (const lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__9_value;
static const lean_string_object l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__10 = (const lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__10_value;
static const lean_ctor_object l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__11_value_aux_0),((lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__11_value_aux_1),((lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__11_value_aux_2),((lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__11 = (const lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__11_value;
lean_object* l_Lean_mkAtom(lean_object*);
static lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__12;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__13;
static const lean_string_object l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__14 = (const lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__14_value;
static const lean_string_object l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fun"};
static const lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__15 = (const lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__15_value;
static const lean_ctor_object l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__16_value_aux_0),((lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__16_value_aux_1),((lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__16_value_aux_2),((lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(249, 155, 133, 242, 71, 132, 191, 97)}};
static const lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__16 = (const lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__16_value;
static lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__17;
static lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__18;
static const lean_string_object l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "basicFun"};
static const lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__19 = (const lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__19_value;
static const lean_ctor_object l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__20_value_aux_0),((lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__20_value_aux_1),((lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__20_value_aux_2),((lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(209, 134, 40, 160, 122, 195, 31, 223)}};
static const lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__20 = (const lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__20_value;
static const lean_string_object l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "a"};
static const lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__21 = (const lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__21_value;
lean_object* lean_string_utf8_byte_size(lean_object*);
static lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__22;
static lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__23;
static const lean_ctor_object l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(247, 80, 99, 121, 74, 33, 203, 108)}};
static const lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__24 = (const lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__24_value;
static lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__25;
static lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__26;
static const lean_string_object l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "b"};
static const lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__27 = (const lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__27_value;
static lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__28;
static lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__29;
static const lean_ctor_object l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__27_value),LEAN_SCALAR_PTR_LITERAL(47, 22, 244, 233, 226, 169, 241, 142)}};
static const lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__30 = (const lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__30_value;
static lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__31;
static lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__32;
static lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__33;
static lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__34;
static lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__35;
static lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__36;
static const lean_string_object l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__37 = (const lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__37_value;
static lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__38;
static lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__39;
static const lean_string_object l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 7, .m_data = "term_≤_"};
static const lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__40 = (const lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__40_value;
static const lean_ctor_object l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__40_value),LEAN_SCALAR_PTR_LITERAL(111, 3, 61, 112, 38, 138, 106, 121)}};
static const lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__41 = (const lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__41_value;
static const lean_string_object l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "≤"};
static const lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__42 = (const lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__42_value;
static lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__43;
static lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__44;
static lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__45;
static lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__46;
static lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__47;
static lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__48;
static lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__49;
static lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__50;
static lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__51;
static lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__52;
static lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__53;
static lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__54;
static lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__55;
static lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__56;
static lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__57;
static lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__58;
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_List_MergeSort_Internal_splitInTwo___redArg(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run_match__3_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_mergeSortTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_mergeSortTR(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_splitRevInTwo___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_splitRevInTwo___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_splitRevInTwo(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_splitRevInTwo___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_splitRevInTwo_x27___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_splitRevInTwo_x27___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_splitRevInTwo_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_splitRevInTwo_x27___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_mergeSortTR_u2082___auto__1;
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run_x27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run_x27___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run_x27(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run_x27_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run_x27_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run_x27_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_mergeSortTR_u2082___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_mergeSortTR_u2082(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_mergeSort_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_mergeSort_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeTR_go___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; 
lean_dec_ref(x_1);
x_5 = l_List_reverseAux___redArg(x_4, x_3);
return x_5;
}
else
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_6; 
lean_dec_ref(x_1);
x_6 = l_List_reverseAux___redArg(x_4, x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_1);
lean_inc(x_9);
lean_inc(x_7);
x_11 = lean_apply_2(x_1, x_7, x_9);
x_12 = lean_unbox(x_11);
if (x_12 == 0)
{
uint8_t x_13; 
lean_inc(x_10);
lean_inc(x_9);
x_13 = !lean_is_exclusive(x_3);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_3, 1);
lean_dec(x_14);
x_15 = lean_ctor_get(x_3, 0);
lean_dec(x_15);
lean_ctor_set(x_3, 1, x_4);
{
lean_object* _tmp_2 = x_10;
lean_object* _tmp_3 = x_3;
x_3 = _tmp_2;
x_4 = _tmp_3;
}
goto _start;
}
else
{
lean_object* x_17; 
lean_dec(x_3);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_4);
x_3 = x_10;
x_4 = x_17;
goto _start;
}
}
else
{
uint8_t x_19; 
lean_inc(x_8);
lean_inc(x_7);
x_19 = !lean_is_exclusive(x_2);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_2, 1);
lean_dec(x_20);
x_21 = lean_ctor_get(x_2, 0);
lean_dec(x_21);
lean_ctor_set(x_2, 1, x_4);
{
lean_object* _tmp_1 = x_8;
lean_object* _tmp_3 = x_2;
x_2 = _tmp_1;
x_4 = _tmp_3;
}
goto _start;
}
else
{
lean_object* x_23; 
lean_dec(x_2);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_7);
lean_ctor_set(x_23, 1, x_4);
x_2 = x_8;
x_4 = x_23;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeTR_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeTR_go___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeTR_go_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_7; 
lean_dec(x_6);
lean_dec(x_5);
x_7 = lean_apply_2(x_4, x_2, x_3);
return x_7;
}
else
{
lean_dec(x_4);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_8; 
lean_dec(x_6);
x_8 = lean_apply_3(x_5, x_1, x_3, lean_box(0));
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec_ref(x_1);
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec_ref(x_2);
x_13 = lean_apply_5(x_6, x_9, x_10, x_11, x_12, x_3);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeTR_go_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_9; 
lean_dec(x_8);
lean_dec(x_7);
x_9 = lean_apply_2(x_6, x_4, x_5);
return x_9;
}
else
{
lean_dec(x_6);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_10; 
lean_dec(x_8);
x_10 = lean_apply_3(x_7, x_3, x_5, lean_box(0));
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_7);
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_dec_ref(x_3);
x_13 = lean_ctor_get(x_4, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
lean_dec_ref(x_4);
x_15 = lean_apply_5(x_8, x_11, x_12, x_13, x_14, x_5);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_mergeTR___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeTR_go___redArg(x_3, x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_mergeTR(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_MergeSort_Internal_mergeTR___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_merge_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; 
lean_dec(x_5);
lean_dec(x_4);
x_6 = lean_apply_1(x_3, x_2);
return x_6;
}
else
{
lean_dec(x_3);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_7; 
lean_dec(x_5);
x_7 = lean_apply_2(x_4, x_1, lean_box(0));
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec_ref(x_1);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_dec_ref(x_2);
x_12 = lean_apply_4(x_5, x_8, x_9, x_10, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_merge_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_8; 
lean_dec(x_7);
lean_dec(x_6);
x_8 = lean_apply_1(x_5, x_4);
return x_8;
}
else
{
lean_dec(x_5);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_9; 
lean_dec(x_7);
x_9 = lean_apply_2(x_6, x_3, lean_box(0));
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_dec_ref(x_3);
x_12 = lean_ctor_get(x_4, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
lean_dec_ref(x_4);
x_14 = lean_apply_4(x_7, x_10, x_11, x_12, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_splitRevAt_go___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_2, x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_inc(x_5);
lean_inc(x_4);
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 1);
lean_dec(x_9);
x_10 = lean_ctor_get(x_1, 0);
lean_dec(x_10);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_2, x_11);
lean_dec(x_2);
lean_ctor_set(x_1, 1, x_3);
{
lean_object* _tmp_0 = x_5;
lean_object* _tmp_1 = x_12;
lean_object* _tmp_2 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_2, x_14);
lean_dec(x_2);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_4);
lean_ctor_set(x_16, 1, x_3);
x_1 = x_5;
x_2 = x_15;
x_3 = x_16;
goto _start;
}
}
else
{
lean_object* x_18; 
lean_dec(x_2);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_3);
lean_ctor_set(x_18, 1, x_1);
return x_18;
}
}
else
{
lean_object* x_19; 
lean_dec(x_2);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_3);
lean_ctor_set(x_19, 1, x_1);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_splitRevAt_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_splitRevAt_go___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_splitRevAt___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_splitRevAt_go___redArg(x_2, x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_splitRevAt(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_MergeSort_Internal_splitRevAt___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_splitRevAt_go_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_2, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_2, x_10);
lean_dec(x_2);
x_12 = lean_apply_4(x_4, x_6, x_7, x_11, x_3);
return x_12;
}
else
{
lean_object* x_13; 
lean_dec(x_4);
x_13 = lean_apply_4(x_5, x_1, x_2, x_3, lean_box(0));
return x_13;
}
}
else
{
lean_object* x_14; 
lean_dec(x_4);
x_14 = lean_apply_4(x_5, x_1, x_2, x_3, lean_box(0));
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_splitRevAt_go_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_4, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_7);
lean_dec_ref(x_3);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_4, x_12);
lean_dec(x_4);
x_14 = lean_apply_4(x_6, x_8, x_9, x_13, x_5);
return x_14;
}
else
{
lean_object* x_15; 
lean_dec(x_6);
x_15 = lean_apply_4(x_7, x_3, x_4, x_5, lean_box(0));
return x_15;
}
}
else
{
lean_object* x_16; 
lean_dec(x_6);
x_16 = lean_apply_4(x_7, x_3, x_4, x_5, lean_box(0));
return x_16;
}
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__10));
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__12;
x_2 = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__5;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__15));
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__17;
x_2 = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__5;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__21));
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__22;
x_2 = lean_unsigned_to_nat(0u);
x_3 = ((lean_object*)(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__21));
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__24));
x_3 = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__23;
x_4 = lean_box(2);
x_5 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__25;
x_2 = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__5;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__27));
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__28;
x_2 = lean_unsigned_to_nat(0u);
x_3 = ((lean_object*)(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__27));
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__30));
x_3 = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__29;
x_4 = lean_box(2);
x_5 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__31;
x_2 = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__26;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__32;
x_2 = ((lean_object*)(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__9));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__33;
x_2 = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__5;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__35() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__5;
x_2 = ((lean_object*)(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__9));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__35;
x_2 = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__34;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__38() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__37));
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__39() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__38;
x_2 = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__36;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__43() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__42));
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__44() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__43;
x_2 = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__26;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__45() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__31;
x_2 = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__44;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__46() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__45;
x_2 = ((lean_object*)(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__41));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__47() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__46;
x_2 = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__39;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__48() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__47;
x_2 = ((lean_object*)(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__20));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__49() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__48;
x_2 = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__18;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__50() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__49;
x_2 = ((lean_object*)(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__16));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__51() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__50;
x_2 = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__13;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__52() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__51;
x_2 = ((lean_object*)(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__11));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__53() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__52;
x_2 = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__5;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__54() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__53;
x_2 = ((lean_object*)(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__9));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__55() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__54;
x_2 = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__5;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__56() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__55;
x_2 = ((lean_object*)(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__7));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__57() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__56;
x_2 = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__5;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__58() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__57;
x_2 = ((lean_object*)(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__4));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1() {
_start:
{
lean_object* x_1; 
x_1 = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__58;
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_2, x_4);
if (x_5 == 1)
{
lean_dec_ref(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_2, x_6);
x_8 = lean_nat_dec_eq(x_7, x_4);
if (x_8 == 1)
{
lean_dec(x_7);
lean_dec_ref(x_1);
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_9 = lean_nat_sub(x_7, x_6);
lean_dec(x_7);
x_10 = lean_unsigned_to_nat(2u);
x_11 = lean_nat_add(x_9, x_10);
lean_dec(x_9);
x_12 = l_List_MergeSort_Internal_splitInTwo___redArg(x_11, x_3);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = lean_nat_add(x_11, x_6);
x_16 = lean_nat_shiftr(x_15, x_6);
lean_dec(x_15);
lean_inc_ref(x_1);
x_17 = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run___redArg(x_1, x_16, x_13);
lean_dec(x_16);
x_18 = lean_nat_shiftr(x_11, x_6);
lean_dec(x_11);
lean_inc_ref(x_1);
x_19 = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run___redArg(x_1, x_18, x_14);
lean_dec(x_18);
x_20 = l_List_MergeSort_Internal_mergeTR___redArg(x_17, x_19, x_1);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run_match__3_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_1, x_6);
if (x_7 == 1)
{
lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_8 = lean_apply_1(x_3, lean_box(0));
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
lean_dec(x_3);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_1, x_9);
x_11 = lean_nat_dec_eq(x_10, x_6);
if (x_11 == 1)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_5);
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_apply_2(x_4, x_12, lean_box(0));
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
x_14 = lean_nat_sub(x_10, x_9);
lean_dec(x_10);
x_15 = lean_apply_2(x_5, x_14, x_2);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run_match__3_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run_match__3_splitter___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run_match__3_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run_match__3_splitter___redArg(x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run_match__3_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run_match__3_splitter(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run_match__1_splitter___redArg(x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run_match__1_splitter(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_mergeSortTR___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_List_lengthTR___redArg(x_1);
x_4 = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run___redArg(x_2, x_3, x_1);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_mergeSortTR(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_MergeSort_Internal_mergeSortTR___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_splitRevInTwo___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_add(x_1, x_3);
x_5 = lean_nat_shiftr(x_4, x_3);
lean_dec(x_4);
x_6 = l_List_MergeSort_Internal_splitRevAt___redArg(x_5, x_2);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_splitRevInTwo___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_MergeSort_Internal_splitRevInTwo___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_splitRevInTwo(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_MergeSort_Internal_splitRevInTwo___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_splitRevInTwo___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_MergeSort_Internal_splitRevInTwo(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_splitRevInTwo_x27___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_shiftr(x_1, x_3);
x_5 = l_List_MergeSort_Internal_splitRevAt___redArg(x_4, x_2);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_splitRevInTwo_x27___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_MergeSort_Internal_splitRevInTwo_x27___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_splitRevInTwo_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_MergeSort_Internal_splitRevInTwo_x27___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_splitRevInTwo_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_MergeSort_Internal_splitRevInTwo_x27(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR_u2082___auto__1() {
_start:
{
lean_object* x_1; 
x_1 = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__58;
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_2, x_4);
if (x_5 == 1)
{
lean_dec_ref(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_2, x_6);
x_8 = lean_nat_dec_eq(x_7, x_4);
if (x_8 == 1)
{
lean_dec(x_7);
lean_dec_ref(x_1);
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_9 = lean_nat_sub(x_7, x_6);
lean_dec(x_7);
x_10 = lean_unsigned_to_nat(2u);
x_11 = lean_nat_add(x_9, x_10);
lean_dec(x_9);
x_12 = l_List_MergeSort_Internal_splitRevInTwo___redArg(x_11, x_3);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = lean_nat_add(x_11, x_6);
x_16 = lean_nat_shiftr(x_15, x_6);
lean_dec(x_15);
lean_inc_ref(x_1);
x_17 = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run_x27___redArg(x_1, x_16, x_13);
lean_dec(x_16);
x_18 = lean_nat_shiftr(x_11, x_6);
lean_dec(x_11);
lean_inc_ref(x_1);
x_19 = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run___redArg(x_1, x_18, x_14);
lean_dec(x_18);
x_20 = l_List_MergeSort_Internal_mergeTR___redArg(x_17, x_19, x_1);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run_x27___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_2, x_4);
if (x_5 == 1)
{
lean_dec_ref(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_2, x_6);
x_8 = lean_nat_dec_eq(x_7, x_4);
if (x_8 == 1)
{
lean_dec(x_7);
lean_dec_ref(x_1);
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_9 = lean_nat_sub(x_7, x_6);
lean_dec(x_7);
x_10 = lean_unsigned_to_nat(2u);
x_11 = lean_nat_add(x_9, x_10);
lean_dec(x_9);
x_12 = l_List_MergeSort_Internal_splitRevInTwo_x27___redArg(x_11, x_3);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = lean_nat_add(x_11, x_6);
x_16 = lean_nat_shiftr(x_15, x_6);
lean_dec(x_15);
lean_inc_ref(x_1);
x_17 = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run_x27___redArg(x_1, x_16, x_14);
lean_dec(x_16);
x_18 = lean_nat_shiftr(x_11, x_6);
lean_dec(x_11);
lean_inc_ref(x_1);
x_19 = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run___redArg(x_1, x_18, x_13);
lean_dec(x_18);
x_20 = l_List_MergeSort_Internal_mergeTR___redArg(x_17, x_19, x_1);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run_x27___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run_x27___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run_x27___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run_x27(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run_x27_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run_x27_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run_x27_match__1_splitter___redArg(x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run_x27_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run_x27_match__1_splitter(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_mergeSortTR_u2082___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_List_lengthTR___redArg(x_1);
x_4 = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run___redArg(x_2, x_3, x_1);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_mergeSortTR_u2082(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_MergeSort_Internal_mergeSortTR_u2082___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_mergeSort_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; 
lean_dec(x_5);
lean_dec(x_4);
x_6 = lean_apply_1(x_3, x_2);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_3);
x_7 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec_ref(x_1);
x_9 = lean_apply_2(x_4, x_8, x_2);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_inc_ref(x_7);
lean_dec(x_4);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec_ref(x_1);
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_dec_ref(x_7);
x_13 = lean_apply_4(x_5, x_10, x_11, x_12, x_2);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_mergeSort_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_List_Sort_Impl_0__List_mergeSort_match__1_splitter___redArg(x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* initialize_Init_Data_List_Sort_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_List_Sort_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_List_Sort_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Linear(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_List_Sort_Impl(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_List_Sort_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Sort_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Sort_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__5 = _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__5();
lean_mark_persistent(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__5);
l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__12 = _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__12();
lean_mark_persistent(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__12);
l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__13 = _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__13();
lean_mark_persistent(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__13);
l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__17 = _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__17();
lean_mark_persistent(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__17);
l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__18 = _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__18();
lean_mark_persistent(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__18);
l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__22 = _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__22();
lean_mark_persistent(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__22);
l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__23 = _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__23();
lean_mark_persistent(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__23);
l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__25 = _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__25();
lean_mark_persistent(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__25);
l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__26 = _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__26();
lean_mark_persistent(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__26);
l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__28 = _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__28();
lean_mark_persistent(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__28);
l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__29 = _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__29();
lean_mark_persistent(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__29);
l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__31 = _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__31();
lean_mark_persistent(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__31);
l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__32 = _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__32();
lean_mark_persistent(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__32);
l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__33 = _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__33();
lean_mark_persistent(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__33);
l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__34 = _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__34();
lean_mark_persistent(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__34);
l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__35 = _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__35();
lean_mark_persistent(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__35);
l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__36 = _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__36();
lean_mark_persistent(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__36);
l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__38 = _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__38();
lean_mark_persistent(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__38);
l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__39 = _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__39();
lean_mark_persistent(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__39);
l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__43 = _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__43();
lean_mark_persistent(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__43);
l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__44 = _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__44();
lean_mark_persistent(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__44);
l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__45 = _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__45();
lean_mark_persistent(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__45);
l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__46 = _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__46();
lean_mark_persistent(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__46);
l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__47 = _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__47();
lean_mark_persistent(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__47);
l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__48 = _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__48();
lean_mark_persistent(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__48);
l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__49 = _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__49();
lean_mark_persistent(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__49);
l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__50 = _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__50();
lean_mark_persistent(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__50);
l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__51 = _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__51();
lean_mark_persistent(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__51);
l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__52 = _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__52();
lean_mark_persistent(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__52);
l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__53 = _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__53();
lean_mark_persistent(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__53);
l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__54 = _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__54();
lean_mark_persistent(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__54);
l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__55 = _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__55();
lean_mark_persistent(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__55);
l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__56 = _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__56();
lean_mark_persistent(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__56);
l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__57 = _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__57();
lean_mark_persistent(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__57);
l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__58 = _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__58();
lean_mark_persistent(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__58);
l_List_MergeSort_Internal_mergeSortTR___auto__1 = _init_l_List_MergeSort_Internal_mergeSortTR___auto__1();
lean_mark_persistent(l_List_MergeSort_Internal_mergeSortTR___auto__1);
l_List_MergeSort_Internal_mergeSortTR_u2082___auto__1 = _init_l_List_MergeSort_Internal_mergeSortTR_u2082___auto__1();
lean_mark_persistent(l_List_MergeSort_Internal_mergeSortTR_u2082___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

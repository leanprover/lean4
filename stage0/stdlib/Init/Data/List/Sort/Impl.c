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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_List_MergeSort_Internal_splitInTwo___redArg(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_List_reverseAux___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeTR_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeTR_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeTR_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeTR_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_mergeTR___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_mergeTR(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_merge_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_merge_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__4_value_aux_0),((lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__4_value_aux_1),((lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__4_value_aux_2),((lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__4 = (const lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__4_value;
static const lean_array_object l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__5 = (const lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__5_value;
static const lean_string_object l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__6 = (const lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__6_value;
static const lean_ctor_object l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__7_value_aux_0),((lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__7_value_aux_1),((lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__7_value_aux_2),((lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__7 = (const lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__7_value;
static const lean_string_object l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__8 = (const lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__8_value;
static const lean_ctor_object l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__9 = (const lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__9_value;
static const lean_string_object l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__10 = (const lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__10_value;
static const lean_ctor_object l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__11_value_aux_0),((lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__11_value_aux_1),((lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__11_value_aux_2),((lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__11 = (const lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__11_value;
static lean_once_cell_t l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__12;
static lean_once_cell_t l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
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
static lean_once_cell_t l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__17;
static lean_once_cell_t l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
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
static lean_once_cell_t l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__22;
static lean_once_cell_t l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__23;
static const lean_ctor_object l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(247, 80, 99, 121, 74, 33, 203, 108)}};
static const lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__24 = (const lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__24_value;
static lean_once_cell_t l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__25;
static lean_once_cell_t l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__26;
static const lean_string_object l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "b"};
static const lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__27 = (const lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__27_value;
static lean_once_cell_t l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__28;
static lean_once_cell_t l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__29;
static const lean_ctor_object l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__27_value),LEAN_SCALAR_PTR_LITERAL(47, 22, 244, 233, 226, 169, 241, 142)}};
static const lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__30 = (const lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__30_value;
static lean_once_cell_t l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__31;
static lean_once_cell_t l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__32;
static lean_once_cell_t l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__33;
static lean_once_cell_t l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__34;
static const lean_ctor_object l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__9_value),((lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__5_value)}};
static const lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__35 = (const lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__35_value;
static lean_once_cell_t l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__36;
static const lean_string_object l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__37 = (const lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__37_value;
static lean_once_cell_t l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__38;
static lean_once_cell_t l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__39;
static const lean_string_object l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 7, .m_data = "term_≤_"};
static const lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__40 = (const lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__40_value;
static const lean_ctor_object l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__40_value),LEAN_SCALAR_PTR_LITERAL(111, 3, 61, 112, 38, 138, 106, 121)}};
static const lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__41 = (const lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__41_value;
static const lean_string_object l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "≤"};
static const lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__42 = (const lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__42_value;
static lean_once_cell_t l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__43_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__43;
static lean_once_cell_t l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__44;
static lean_once_cell_t l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__45;
static lean_once_cell_t l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__46_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__46;
static lean_once_cell_t l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__47_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__47;
static lean_once_cell_t l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__48_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__48;
static lean_once_cell_t l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__49_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__49;
static lean_once_cell_t l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__50_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__50;
static lean_once_cell_t l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__51_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__51;
static lean_once_cell_t l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__52_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__52;
static lean_once_cell_t l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__53_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__53;
static lean_once_cell_t l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__54_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__54;
static lean_once_cell_t l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__55_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__55;
static lean_once_cell_t l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__56_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__56;
static lean_once_cell_t l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__57_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__57;
static lean_once_cell_t l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__58_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__58;
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1;
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
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run_x27___redArg(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeTR_go___redArg(lean_object* v_le_1_, lean_object* v_a_2_, lean_object* v_a_3_, lean_object* v_a_4_){
_start:
{
if (lean_obj_tag(v_a_2_) == 0)
{
lean_object* v___x_5_; 
lean_dec_ref(v_le_1_);
v___x_5_ = l_List_reverseAux___redArg(v_a_4_, v_a_3_);
return v___x_5_;
}
else
{
if (lean_obj_tag(v_a_3_) == 0)
{
lean_object* v___x_6_; 
lean_dec_ref(v_le_1_);
v___x_6_ = l_List_reverseAux___redArg(v_a_4_, v_a_2_);
return v___x_6_;
}
else
{
lean_object* v_head_7_; lean_object* v_tail_8_; lean_object* v_head_9_; lean_object* v_tail_10_; lean_object* v___x_11_; uint8_t v___x_12_; 
v_head_7_ = lean_ctor_get(v_a_2_, 0);
v_tail_8_ = lean_ctor_get(v_a_2_, 1);
v_head_9_ = lean_ctor_get(v_a_3_, 0);
v_tail_10_ = lean_ctor_get(v_a_3_, 1);
lean_inc_ref(v_le_1_);
lean_inc(v_head_9_);
lean_inc(v_head_7_);
v___x_11_ = lean_apply_2(v_le_1_, v_head_7_, v_head_9_);
v___x_12_ = lean_unbox(v___x_11_);
if (v___x_12_ == 0)
{
lean_object* v___x_14_; uint8_t v_isShared_15_; uint8_t v_isSharedCheck_20_; 
lean_inc(v_tail_10_);
lean_inc(v_head_9_);
v_isSharedCheck_20_ = !lean_is_exclusive(v_a_3_);
if (v_isSharedCheck_20_ == 0)
{
lean_object* v_unused_21_; lean_object* v_unused_22_; 
v_unused_21_ = lean_ctor_get(v_a_3_, 1);
lean_dec(v_unused_21_);
v_unused_22_ = lean_ctor_get(v_a_3_, 0);
lean_dec(v_unused_22_);
v___x_14_ = v_a_3_;
v_isShared_15_ = v_isSharedCheck_20_;
goto v_resetjp_13_;
}
else
{
lean_dec(v_a_3_);
v___x_14_ = lean_box(0);
v_isShared_15_ = v_isSharedCheck_20_;
goto v_resetjp_13_;
}
v_resetjp_13_:
{
lean_object* v___x_17_; 
if (v_isShared_15_ == 0)
{
lean_ctor_set(v___x_14_, 1, v_a_4_);
v___x_17_ = v___x_14_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_19_; 
v_reuseFailAlloc_19_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_19_, 0, v_head_9_);
lean_ctor_set(v_reuseFailAlloc_19_, 1, v_a_4_);
v___x_17_ = v_reuseFailAlloc_19_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
v_a_3_ = v_tail_10_;
v_a_4_ = v___x_17_;
goto _start;
}
}
}
else
{
lean_object* v___x_24_; uint8_t v_isShared_25_; uint8_t v_isSharedCheck_30_; 
lean_inc(v_tail_8_);
lean_inc(v_head_7_);
v_isSharedCheck_30_ = !lean_is_exclusive(v_a_2_);
if (v_isSharedCheck_30_ == 0)
{
lean_object* v_unused_31_; lean_object* v_unused_32_; 
v_unused_31_ = lean_ctor_get(v_a_2_, 1);
lean_dec(v_unused_31_);
v_unused_32_ = lean_ctor_get(v_a_2_, 0);
lean_dec(v_unused_32_);
v___x_24_ = v_a_2_;
v_isShared_25_ = v_isSharedCheck_30_;
goto v_resetjp_23_;
}
else
{
lean_dec(v_a_2_);
v___x_24_ = lean_box(0);
v_isShared_25_ = v_isSharedCheck_30_;
goto v_resetjp_23_;
}
v_resetjp_23_:
{
lean_object* v___x_27_; 
if (v_isShared_25_ == 0)
{
lean_ctor_set(v___x_24_, 1, v_a_4_);
v___x_27_ = v___x_24_;
goto v_reusejp_26_;
}
else
{
lean_object* v_reuseFailAlloc_29_; 
v_reuseFailAlloc_29_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_29_, 0, v_head_7_);
lean_ctor_set(v_reuseFailAlloc_29_, 1, v_a_4_);
v___x_27_ = v_reuseFailAlloc_29_;
goto v_reusejp_26_;
}
v_reusejp_26_:
{
v_a_2_ = v_tail_8_;
v_a_4_ = v___x_27_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeTR_go(lean_object* v_00_u03b1_33_, lean_object* v_le_34_, lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeTR_go___redArg(v_le_34_, v_a_35_, v_a_36_, v_a_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeTR_go_match__1_splitter___redArg(lean_object* v_x_39_, lean_object* v_x_40_, lean_object* v_x_41_, lean_object* v_h__1_42_, lean_object* v_h__2_43_, lean_object* v_h__3_44_){
_start:
{
if (lean_obj_tag(v_x_39_) == 0)
{
lean_object* v___x_45_; 
lean_dec(v_h__3_44_);
lean_dec(v_h__2_43_);
v___x_45_ = lean_apply_2(v_h__1_42_, v_x_40_, v_x_41_);
return v___x_45_;
}
else
{
lean_dec(v_h__1_42_);
if (lean_obj_tag(v_x_40_) == 0)
{
lean_object* v___x_46_; 
lean_dec(v_h__3_44_);
v___x_46_ = lean_apply_3(v_h__2_43_, v_x_39_, v_x_41_, lean_box(0));
return v___x_46_;
}
else
{
lean_object* v_head_47_; lean_object* v_tail_48_; lean_object* v_head_49_; lean_object* v_tail_50_; lean_object* v___x_51_; 
lean_dec(v_h__2_43_);
v_head_47_ = lean_ctor_get(v_x_39_, 0);
lean_inc(v_head_47_);
v_tail_48_ = lean_ctor_get(v_x_39_, 1);
lean_inc(v_tail_48_);
lean_dec_ref(v_x_39_);
v_head_49_ = lean_ctor_get(v_x_40_, 0);
lean_inc(v_head_49_);
v_tail_50_ = lean_ctor_get(v_x_40_, 1);
lean_inc(v_tail_50_);
lean_dec_ref(v_x_40_);
v___x_51_ = lean_apply_5(v_h__3_44_, v_head_47_, v_tail_48_, v_head_49_, v_tail_50_, v_x_41_);
return v___x_51_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeTR_go_match__1_splitter(lean_object* v_00_u03b1_52_, lean_object* v_motive_53_, lean_object* v_x_54_, lean_object* v_x_55_, lean_object* v_x_56_, lean_object* v_h__1_57_, lean_object* v_h__2_58_, lean_object* v_h__3_59_){
_start:
{
if (lean_obj_tag(v_x_54_) == 0)
{
lean_object* v___x_60_; 
lean_dec(v_h__3_59_);
lean_dec(v_h__2_58_);
v___x_60_ = lean_apply_2(v_h__1_57_, v_x_55_, v_x_56_);
return v___x_60_;
}
else
{
lean_dec(v_h__1_57_);
if (lean_obj_tag(v_x_55_) == 0)
{
lean_object* v___x_61_; 
lean_dec(v_h__3_59_);
v___x_61_ = lean_apply_3(v_h__2_58_, v_x_54_, v_x_56_, lean_box(0));
return v___x_61_;
}
else
{
lean_object* v_head_62_; lean_object* v_tail_63_; lean_object* v_head_64_; lean_object* v_tail_65_; lean_object* v___x_66_; 
lean_dec(v_h__2_58_);
v_head_62_ = lean_ctor_get(v_x_54_, 0);
lean_inc(v_head_62_);
v_tail_63_ = lean_ctor_get(v_x_54_, 1);
lean_inc(v_tail_63_);
lean_dec_ref(v_x_54_);
v_head_64_ = lean_ctor_get(v_x_55_, 0);
lean_inc(v_head_64_);
v_tail_65_ = lean_ctor_get(v_x_55_, 1);
lean_inc(v_tail_65_);
lean_dec_ref(v_x_55_);
v___x_66_ = lean_apply_5(v_h__3_59_, v_head_62_, v_tail_63_, v_head_64_, v_tail_65_, v_x_56_);
return v___x_66_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_mergeTR___redArg(lean_object* v_l_u2081_67_, lean_object* v_l_u2082_68_, lean_object* v_le_69_){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_70_ = lean_box(0);
v___x_71_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeTR_go___redArg(v_le_69_, v_l_u2081_67_, v_l_u2082_68_, v___x_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_mergeTR(lean_object* v_00_u03b1_72_, lean_object* v_l_u2081_73_, lean_object* v_l_u2082_74_, lean_object* v_le_75_){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = l_List_MergeSort_Internal_mergeTR___redArg(v_l_u2081_73_, v_l_u2082_74_, v_le_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_merge_match__1_splitter___redArg(lean_object* v_xs_77_, lean_object* v_ys_78_, lean_object* v_h__1_79_, lean_object* v_h__2_80_, lean_object* v_h__3_81_){
_start:
{
if (lean_obj_tag(v_xs_77_) == 0)
{
lean_object* v___x_82_; 
lean_dec(v_h__3_81_);
lean_dec(v_h__2_80_);
v___x_82_ = lean_apply_1(v_h__1_79_, v_ys_78_);
return v___x_82_;
}
else
{
lean_dec(v_h__1_79_);
if (lean_obj_tag(v_ys_78_) == 0)
{
lean_object* v___x_83_; 
lean_dec(v_h__3_81_);
v___x_83_ = lean_apply_2(v_h__2_80_, v_xs_77_, lean_box(0));
return v___x_83_;
}
else
{
lean_object* v_head_84_; lean_object* v_tail_85_; lean_object* v_head_86_; lean_object* v_tail_87_; lean_object* v___x_88_; 
lean_dec(v_h__2_80_);
v_head_84_ = lean_ctor_get(v_xs_77_, 0);
lean_inc(v_head_84_);
v_tail_85_ = lean_ctor_get(v_xs_77_, 1);
lean_inc(v_tail_85_);
lean_dec_ref(v_xs_77_);
v_head_86_ = lean_ctor_get(v_ys_78_, 0);
lean_inc(v_head_86_);
v_tail_87_ = lean_ctor_get(v_ys_78_, 1);
lean_inc(v_tail_87_);
lean_dec_ref(v_ys_78_);
v___x_88_ = lean_apply_4(v_h__3_81_, v_head_84_, v_tail_85_, v_head_86_, v_tail_87_);
return v___x_88_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_merge_match__1_splitter(lean_object* v_00_u03b1_89_, lean_object* v_motive_90_, lean_object* v_xs_91_, lean_object* v_ys_92_, lean_object* v_h__1_93_, lean_object* v_h__2_94_, lean_object* v_h__3_95_){
_start:
{
if (lean_obj_tag(v_xs_91_) == 0)
{
lean_object* v___x_96_; 
lean_dec(v_h__3_95_);
lean_dec(v_h__2_94_);
v___x_96_ = lean_apply_1(v_h__1_93_, v_ys_92_);
return v___x_96_;
}
else
{
lean_dec(v_h__1_93_);
if (lean_obj_tag(v_ys_92_) == 0)
{
lean_object* v___x_97_; 
lean_dec(v_h__3_95_);
v___x_97_ = lean_apply_2(v_h__2_94_, v_xs_91_, lean_box(0));
return v___x_97_;
}
else
{
lean_object* v_head_98_; lean_object* v_tail_99_; lean_object* v_head_100_; lean_object* v_tail_101_; lean_object* v___x_102_; 
lean_dec(v_h__2_94_);
v_head_98_ = lean_ctor_get(v_xs_91_, 0);
lean_inc(v_head_98_);
v_tail_99_ = lean_ctor_get(v_xs_91_, 1);
lean_inc(v_tail_99_);
lean_dec_ref(v_xs_91_);
v_head_100_ = lean_ctor_get(v_ys_92_, 0);
lean_inc(v_head_100_);
v_tail_101_ = lean_ctor_get(v_ys_92_, 1);
lean_inc(v_tail_101_);
lean_dec_ref(v_ys_92_);
v___x_102_ = lean_apply_4(v_h__3_95_, v_head_98_, v_tail_99_, v_head_100_, v_tail_101_);
return v___x_102_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_splitRevAt_go___redArg(lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_){
_start:
{
if (lean_obj_tag(v_a_103_) == 1)
{
lean_object* v_head_106_; lean_object* v_tail_107_; lean_object* v_zero_108_; uint8_t v_isZero_109_; 
v_head_106_ = lean_ctor_get(v_a_103_, 0);
v_tail_107_ = lean_ctor_get(v_a_103_, 1);
v_zero_108_ = lean_unsigned_to_nat(0u);
v_isZero_109_ = lean_nat_dec_eq(v_a_104_, v_zero_108_);
if (v_isZero_109_ == 0)
{
lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_119_; 
lean_inc(v_tail_107_);
lean_inc(v_head_106_);
v_isSharedCheck_119_ = !lean_is_exclusive(v_a_103_);
if (v_isSharedCheck_119_ == 0)
{
lean_object* v_unused_120_; lean_object* v_unused_121_; 
v_unused_120_ = lean_ctor_get(v_a_103_, 1);
lean_dec(v_unused_120_);
v_unused_121_ = lean_ctor_get(v_a_103_, 0);
lean_dec(v_unused_121_);
v___x_111_ = v_a_103_;
v_isShared_112_ = v_isSharedCheck_119_;
goto v_resetjp_110_;
}
else
{
lean_dec(v_a_103_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_119_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
lean_object* v_one_113_; lean_object* v_n_114_; lean_object* v___x_116_; 
v_one_113_ = lean_unsigned_to_nat(1u);
v_n_114_ = lean_nat_sub(v_a_104_, v_one_113_);
lean_dec(v_a_104_);
if (v_isShared_112_ == 0)
{
lean_ctor_set(v___x_111_, 1, v_a_105_);
v___x_116_ = v___x_111_;
goto v_reusejp_115_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_118_, 0, v_head_106_);
lean_ctor_set(v_reuseFailAlloc_118_, 1, v_a_105_);
v___x_116_ = v_reuseFailAlloc_118_;
goto v_reusejp_115_;
}
v_reusejp_115_:
{
v_a_103_ = v_tail_107_;
v_a_104_ = v_n_114_;
v_a_105_ = v___x_116_;
goto _start;
}
}
}
else
{
lean_object* v___x_122_; 
lean_dec(v_a_104_);
v___x_122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_122_, 0, v_a_105_);
lean_ctor_set(v___x_122_, 1, v_a_103_);
return v___x_122_;
}
}
else
{
lean_object* v___x_123_; 
lean_dec(v_a_104_);
v___x_123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_123_, 0, v_a_105_);
lean_ctor_set(v___x_123_, 1, v_a_103_);
return v___x_123_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_splitRevAt_go(lean_object* v_00_u03b1_124_, lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_splitRevAt_go___redArg(v_a_125_, v_a_126_, v_a_127_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_splitRevAt___redArg(lean_object* v_n_129_, lean_object* v_l_130_){
_start:
{
lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_131_ = lean_box(0);
v___x_132_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_splitRevAt_go___redArg(v_l_130_, v_n_129_, v___x_131_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_splitRevAt(lean_object* v_00_u03b1_133_, lean_object* v_n_134_, lean_object* v_l_135_){
_start:
{
lean_object* v___x_136_; 
v___x_136_ = l_List_MergeSort_Internal_splitRevAt___redArg(v_n_134_, v_l_135_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_splitRevAt_go_match__1_splitter___redArg(lean_object* v_x_137_, lean_object* v_x_138_, lean_object* v_x_139_, lean_object* v_h__1_140_, lean_object* v_h__2_141_){
_start:
{
if (lean_obj_tag(v_x_137_) == 1)
{
lean_object* v_head_142_; lean_object* v_tail_143_; lean_object* v_zero_144_; uint8_t v_isZero_145_; 
v_head_142_ = lean_ctor_get(v_x_137_, 0);
v_tail_143_ = lean_ctor_get(v_x_137_, 1);
v_zero_144_ = lean_unsigned_to_nat(0u);
v_isZero_145_ = lean_nat_dec_eq(v_x_138_, v_zero_144_);
if (v_isZero_145_ == 0)
{
lean_object* v_one_146_; lean_object* v_n_147_; lean_object* v___x_148_; 
lean_inc(v_tail_143_);
lean_inc(v_head_142_);
lean_dec_ref(v_x_137_);
lean_dec(v_h__2_141_);
v_one_146_ = lean_unsigned_to_nat(1u);
v_n_147_ = lean_nat_sub(v_x_138_, v_one_146_);
lean_dec(v_x_138_);
v___x_148_ = lean_apply_4(v_h__1_140_, v_head_142_, v_tail_143_, v_n_147_, v_x_139_);
return v___x_148_;
}
else
{
lean_object* v___x_149_; 
lean_dec(v_h__1_140_);
v___x_149_ = lean_apply_4(v_h__2_141_, v_x_137_, v_x_138_, v_x_139_, lean_box(0));
return v___x_149_;
}
}
else
{
lean_object* v___x_150_; 
lean_dec(v_h__1_140_);
v___x_150_ = lean_apply_4(v_h__2_141_, v_x_137_, v_x_138_, v_x_139_, lean_box(0));
return v___x_150_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_splitRevAt_go_match__1_splitter(lean_object* v_00_u03b1_151_, lean_object* v_motive_152_, lean_object* v_x_153_, lean_object* v_x_154_, lean_object* v_x_155_, lean_object* v_h__1_156_, lean_object* v_h__2_157_){
_start:
{
if (lean_obj_tag(v_x_153_) == 1)
{
lean_object* v_head_158_; lean_object* v_tail_159_; lean_object* v_zero_160_; uint8_t v_isZero_161_; 
v_head_158_ = lean_ctor_get(v_x_153_, 0);
v_tail_159_ = lean_ctor_get(v_x_153_, 1);
v_zero_160_ = lean_unsigned_to_nat(0u);
v_isZero_161_ = lean_nat_dec_eq(v_x_154_, v_zero_160_);
if (v_isZero_161_ == 0)
{
lean_object* v_one_162_; lean_object* v_n_163_; lean_object* v___x_164_; 
lean_inc(v_tail_159_);
lean_inc(v_head_158_);
lean_dec_ref(v_x_153_);
lean_dec(v_h__2_157_);
v_one_162_ = lean_unsigned_to_nat(1u);
v_n_163_ = lean_nat_sub(v_x_154_, v_one_162_);
lean_dec(v_x_154_);
v___x_164_ = lean_apply_4(v_h__1_156_, v_head_158_, v_tail_159_, v_n_163_, v_x_155_);
return v___x_164_;
}
else
{
lean_object* v___x_165_; 
lean_dec(v_h__1_156_);
v___x_165_ = lean_apply_4(v_h__2_157_, v_x_153_, v_x_154_, v_x_155_, lean_box(0));
return v___x_165_;
}
}
else
{
lean_object* v___x_166_; 
lean_dec(v_h__1_156_);
v___x_166_ = lean_apply_4(v_h__2_157_, v_x_153_, v_x_154_, v_x_155_, lean_box(0));
return v___x_166_;
}
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__12(void){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_193_ = ((lean_object*)(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__10));
v___x_194_ = l_Lean_mkAtom(v___x_193_);
return v___x_194_;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__13(void){
_start:
{
lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_195_ = lean_obj_once(&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__12, &l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__12_once, _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__12);
v___x_196_ = ((lean_object*)(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__5));
v___x_197_ = lean_array_push(v___x_196_, v___x_195_);
return v___x_197_;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__17(void){
_start:
{
lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_205_ = ((lean_object*)(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__15));
v___x_206_ = l_Lean_mkAtom(v___x_205_);
return v___x_206_;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__18(void){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_207_ = lean_obj_once(&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__17, &l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__17_once, _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__17);
v___x_208_ = ((lean_object*)(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__5));
v___x_209_ = lean_array_push(v___x_208_, v___x_207_);
return v___x_209_;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__22(void){
_start:
{
lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_217_ = ((lean_object*)(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__21));
v___x_218_ = lean_string_utf8_byte_size(v___x_217_);
return v___x_218_;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__23(void){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_219_ = lean_obj_once(&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__22, &l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__22_once, _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__22);
v___x_220_ = lean_unsigned_to_nat(0u);
v___x_221_ = ((lean_object*)(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__21));
v___x_222_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_222_, 0, v___x_221_);
lean_ctor_set(v___x_222_, 1, v___x_220_);
lean_ctor_set(v___x_222_, 2, v___x_219_);
return v___x_222_;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__25(void){
_start:
{
lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_225_ = lean_box(0);
v___x_226_ = ((lean_object*)(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__24));
v___x_227_ = lean_obj_once(&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__23, &l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__23_once, _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__23);
v___x_228_ = lean_box(2);
v___x_229_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_229_, 0, v___x_228_);
lean_ctor_set(v___x_229_, 1, v___x_227_);
lean_ctor_set(v___x_229_, 2, v___x_226_);
lean_ctor_set(v___x_229_, 3, v___x_225_);
return v___x_229_;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__26(void){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_230_ = lean_obj_once(&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__25, &l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__25_once, _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__25);
v___x_231_ = ((lean_object*)(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__5));
v___x_232_ = lean_array_push(v___x_231_, v___x_230_);
return v___x_232_;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__28(void){
_start:
{
lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_234_ = ((lean_object*)(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__27));
v___x_235_ = lean_string_utf8_byte_size(v___x_234_);
return v___x_235_;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__29(void){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_236_ = lean_obj_once(&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__28, &l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__28_once, _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__28);
v___x_237_ = lean_unsigned_to_nat(0u);
v___x_238_ = ((lean_object*)(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__27));
v___x_239_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_239_, 0, v___x_238_);
lean_ctor_set(v___x_239_, 1, v___x_237_);
lean_ctor_set(v___x_239_, 2, v___x_236_);
return v___x_239_;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__31(void){
_start:
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_242_ = lean_box(0);
v___x_243_ = ((lean_object*)(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__30));
v___x_244_ = lean_obj_once(&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__29, &l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__29_once, _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__29);
v___x_245_ = lean_box(2);
v___x_246_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_246_, 0, v___x_245_);
lean_ctor_set(v___x_246_, 1, v___x_244_);
lean_ctor_set(v___x_246_, 2, v___x_243_);
lean_ctor_set(v___x_246_, 3, v___x_242_);
return v___x_246_;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__32(void){
_start:
{
lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_247_ = lean_obj_once(&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__31, &l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__31_once, _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__31);
v___x_248_ = lean_obj_once(&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__26, &l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__26_once, _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__26);
v___x_249_ = lean_array_push(v___x_248_, v___x_247_);
return v___x_249_;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__33(void){
_start:
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_250_ = lean_obj_once(&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__32, &l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__32_once, _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__32);
v___x_251_ = ((lean_object*)(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__9));
v___x_252_ = lean_box(2);
v___x_253_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_253_, 0, v___x_252_);
lean_ctor_set(v___x_253_, 1, v___x_251_);
lean_ctor_set(v___x_253_, 2, v___x_250_);
return v___x_253_;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__34(void){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_254_ = lean_obj_once(&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__33, &l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__33_once, _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__33);
v___x_255_ = ((lean_object*)(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__5));
v___x_256_ = lean_array_push(v___x_255_, v___x_254_);
return v___x_256_;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__36(void){
_start:
{
lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_261_ = ((lean_object*)(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__35));
v___x_262_ = lean_obj_once(&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__34, &l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__34_once, _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__34);
v___x_263_ = lean_array_push(v___x_262_, v___x_261_);
return v___x_263_;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__38(void){
_start:
{
lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_265_ = ((lean_object*)(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__37));
v___x_266_ = l_Lean_mkAtom(v___x_265_);
return v___x_266_;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__39(void){
_start:
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_267_ = lean_obj_once(&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__38, &l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__38_once, _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__38);
v___x_268_ = lean_obj_once(&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__36, &l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__36_once, _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__36);
v___x_269_ = lean_array_push(v___x_268_, v___x_267_);
return v___x_269_;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__43(void){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_274_ = ((lean_object*)(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__42));
v___x_275_ = l_Lean_mkAtom(v___x_274_);
return v___x_275_;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__44(void){
_start:
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_276_ = lean_obj_once(&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__43, &l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__43_once, _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__43);
v___x_277_ = lean_obj_once(&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__26, &l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__26_once, _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__26);
v___x_278_ = lean_array_push(v___x_277_, v___x_276_);
return v___x_278_;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__45(void){
_start:
{
lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_279_ = lean_obj_once(&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__31, &l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__31_once, _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__31);
v___x_280_ = lean_obj_once(&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__44, &l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__44_once, _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__44);
v___x_281_ = lean_array_push(v___x_280_, v___x_279_);
return v___x_281_;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__46(void){
_start:
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_282_ = lean_obj_once(&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__45, &l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__45_once, _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__45);
v___x_283_ = ((lean_object*)(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__41));
v___x_284_ = lean_box(2);
v___x_285_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_285_, 0, v___x_284_);
lean_ctor_set(v___x_285_, 1, v___x_283_);
lean_ctor_set(v___x_285_, 2, v___x_282_);
return v___x_285_;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__47(void){
_start:
{
lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_286_ = lean_obj_once(&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__46, &l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__46_once, _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__46);
v___x_287_ = lean_obj_once(&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__39, &l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__39_once, _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__39);
v___x_288_ = lean_array_push(v___x_287_, v___x_286_);
return v___x_288_;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__48(void){
_start:
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_289_ = lean_obj_once(&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__47, &l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__47_once, _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__47);
v___x_290_ = ((lean_object*)(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__20));
v___x_291_ = lean_box(2);
v___x_292_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_292_, 0, v___x_291_);
lean_ctor_set(v___x_292_, 1, v___x_290_);
lean_ctor_set(v___x_292_, 2, v___x_289_);
return v___x_292_;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__49(void){
_start:
{
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_293_ = lean_obj_once(&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__48, &l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__48_once, _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__48);
v___x_294_ = lean_obj_once(&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__18, &l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__18_once, _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__18);
v___x_295_ = lean_array_push(v___x_294_, v___x_293_);
return v___x_295_;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__50(void){
_start:
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_296_ = lean_obj_once(&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__49, &l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__49_once, _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__49);
v___x_297_ = ((lean_object*)(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__16));
v___x_298_ = lean_box(2);
v___x_299_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_299_, 0, v___x_298_);
lean_ctor_set(v___x_299_, 1, v___x_297_);
lean_ctor_set(v___x_299_, 2, v___x_296_);
return v___x_299_;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__51(void){
_start:
{
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_300_ = lean_obj_once(&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__50, &l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__50_once, _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__50);
v___x_301_ = lean_obj_once(&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__13, &l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__13_once, _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__13);
v___x_302_ = lean_array_push(v___x_301_, v___x_300_);
return v___x_302_;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__52(void){
_start:
{
lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_303_ = lean_obj_once(&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__51, &l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__51_once, _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__51);
v___x_304_ = ((lean_object*)(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__11));
v___x_305_ = lean_box(2);
v___x_306_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_306_, 0, v___x_305_);
lean_ctor_set(v___x_306_, 1, v___x_304_);
lean_ctor_set(v___x_306_, 2, v___x_303_);
return v___x_306_;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__53(void){
_start:
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_307_ = lean_obj_once(&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__52, &l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__52_once, _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__52);
v___x_308_ = ((lean_object*)(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__5));
v___x_309_ = lean_array_push(v___x_308_, v___x_307_);
return v___x_309_;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__54(void){
_start:
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_310_ = lean_obj_once(&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__53, &l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__53_once, _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__53);
v___x_311_ = ((lean_object*)(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__9));
v___x_312_ = lean_box(2);
v___x_313_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_313_, 0, v___x_312_);
lean_ctor_set(v___x_313_, 1, v___x_311_);
lean_ctor_set(v___x_313_, 2, v___x_310_);
return v___x_313_;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__55(void){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_314_ = lean_obj_once(&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__54, &l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__54_once, _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__54);
v___x_315_ = ((lean_object*)(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__5));
v___x_316_ = lean_array_push(v___x_315_, v___x_314_);
return v___x_316_;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__56(void){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_317_ = lean_obj_once(&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__55, &l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__55_once, _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__55);
v___x_318_ = ((lean_object*)(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__7));
v___x_319_ = lean_box(2);
v___x_320_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_320_, 0, v___x_319_);
lean_ctor_set(v___x_320_, 1, v___x_318_);
lean_ctor_set(v___x_320_, 2, v___x_317_);
return v___x_320_;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__57(void){
_start:
{
lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_321_ = lean_obj_once(&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__56, &l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__56_once, _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__56);
v___x_322_ = ((lean_object*)(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__5));
v___x_323_ = lean_array_push(v___x_322_, v___x_321_);
return v___x_323_;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__58(void){
_start:
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_324_ = lean_obj_once(&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__57, &l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__57_once, _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__57);
v___x_325_ = ((lean_object*)(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__4));
v___x_326_ = lean_box(2);
v___x_327_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_327_, 0, v___x_326_);
lean_ctor_set(v___x_327_, 1, v___x_325_);
lean_ctor_set(v___x_327_, 2, v___x_324_);
return v___x_327_;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1(void){
_start:
{
lean_object* v___x_328_; 
v___x_328_ = lean_obj_once(&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__58, &l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__58_once, _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__58);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run___redArg(lean_object* v_le_329_, lean_object* v_n_330_, lean_object* v_a_331_){
_start:
{
lean_object* v_zero_332_; uint8_t v_isZero_333_; 
v_zero_332_ = lean_unsigned_to_nat(0u);
v_isZero_333_ = lean_nat_dec_eq(v_n_330_, v_zero_332_);
if (v_isZero_333_ == 1)
{
lean_dec_ref(v_le_329_);
return v_a_331_;
}
else
{
lean_object* v_one_334_; lean_object* v_n_335_; uint8_t v_isZero_336_; 
v_one_334_ = lean_unsigned_to_nat(1u);
v_n_335_ = lean_nat_sub(v_n_330_, v_one_334_);
v_isZero_336_ = lean_nat_dec_eq(v_n_335_, v_zero_332_);
if (v_isZero_336_ == 1)
{
lean_dec(v_n_335_);
lean_dec_ref(v_le_329_);
return v_a_331_;
}
else
{
lean_object* v_n_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v_fst_341_; lean_object* v_snd_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v_n_337_ = lean_nat_sub(v_n_335_, v_one_334_);
lean_dec(v_n_335_);
v___x_338_ = lean_unsigned_to_nat(2u);
v___x_339_ = lean_nat_add(v_n_337_, v___x_338_);
lean_dec(v_n_337_);
v___x_340_ = l_List_MergeSort_Internal_splitInTwo___redArg(v___x_339_, v_a_331_);
v_fst_341_ = lean_ctor_get(v___x_340_, 0);
lean_inc(v_fst_341_);
v_snd_342_ = lean_ctor_get(v___x_340_, 1);
lean_inc(v_snd_342_);
lean_dec_ref(v___x_340_);
v___x_343_ = lean_nat_add(v___x_339_, v_one_334_);
v___x_344_ = lean_nat_shiftr(v___x_343_, v_one_334_);
lean_dec(v___x_343_);
lean_inc_ref(v_le_329_);
v___x_345_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run___redArg(v_le_329_, v___x_344_, v_fst_341_);
lean_dec(v___x_344_);
v___x_346_ = lean_nat_shiftr(v___x_339_, v_one_334_);
lean_dec(v___x_339_);
lean_inc_ref(v_le_329_);
v___x_347_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run___redArg(v_le_329_, v___x_346_, v_snd_342_);
lean_dec(v___x_346_);
v___x_348_ = l_List_MergeSort_Internal_mergeTR___redArg(v___x_345_, v___x_347_, v_le_329_);
return v___x_348_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run___redArg___boxed(lean_object* v_le_349_, lean_object* v_n_350_, lean_object* v_a_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run___redArg(v_le_349_, v_n_350_, v_a_351_);
lean_dec(v_n_350_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run(lean_object* v_00_u03b1_353_, lean_object* v_le_354_, lean_object* v_n_355_, lean_object* v_a_356_){
_start:
{
lean_object* v___x_357_; 
v___x_357_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run___redArg(v_le_354_, v_n_355_, v_a_356_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run___boxed(lean_object* v_00_u03b1_358_, lean_object* v_le_359_, lean_object* v_n_360_, lean_object* v_a_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run(v_00_u03b1_358_, v_le_359_, v_n_360_, v_a_361_);
lean_dec(v_n_360_);
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run_match__3_splitter___redArg(lean_object* v_x_363_, lean_object* v_x_364_, lean_object* v_h__1_365_, lean_object* v_h__2_366_, lean_object* v_h__3_367_){
_start:
{
lean_object* v_zero_368_; uint8_t v_isZero_369_; 
v_zero_368_ = lean_unsigned_to_nat(0u);
v_isZero_369_ = lean_nat_dec_eq(v_x_363_, v_zero_368_);
if (v_isZero_369_ == 1)
{
lean_object* v___x_370_; 
lean_dec(v_h__3_367_);
lean_dec(v_h__2_366_);
lean_dec(v_x_364_);
v___x_370_ = lean_apply_1(v_h__1_365_, lean_box(0));
return v___x_370_;
}
else
{
lean_object* v_one_371_; lean_object* v_n_372_; uint8_t v_isZero_373_; 
lean_dec(v_h__1_365_);
v_one_371_ = lean_unsigned_to_nat(1u);
v_n_372_ = lean_nat_sub(v_x_363_, v_one_371_);
v_isZero_373_ = lean_nat_dec_eq(v_n_372_, v_zero_368_);
if (v_isZero_373_ == 1)
{
lean_object* v_head_374_; lean_object* v___x_375_; 
lean_dec(v_n_372_);
lean_dec(v_h__3_367_);
v_head_374_ = lean_ctor_get(v_x_364_, 0);
lean_inc(v_head_374_);
lean_dec(v_x_364_);
v___x_375_ = lean_apply_2(v_h__2_366_, v_head_374_, lean_box(0));
return v___x_375_;
}
else
{
lean_object* v_n_376_; lean_object* v___x_377_; 
lean_dec(v_h__2_366_);
v_n_376_ = lean_nat_sub(v_n_372_, v_one_371_);
lean_dec(v_n_372_);
v___x_377_ = lean_apply_2(v_h__3_367_, v_n_376_, v_x_364_);
return v___x_377_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run_match__3_splitter___redArg___boxed(lean_object* v_x_378_, lean_object* v_x_379_, lean_object* v_h__1_380_, lean_object* v_h__2_381_, lean_object* v_h__3_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run_match__3_splitter___redArg(v_x_378_, v_x_379_, v_h__1_380_, v_h__2_381_, v_h__3_382_);
lean_dec(v_x_378_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run_match__3_splitter(lean_object* v_00_u03b1_384_, lean_object* v_motive_385_, lean_object* v_x_386_, lean_object* v_x_387_, lean_object* v_h__1_388_, lean_object* v_h__2_389_, lean_object* v_h__3_390_){
_start:
{
lean_object* v___x_391_; 
v___x_391_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run_match__3_splitter___redArg(v_x_386_, v_x_387_, v_h__1_388_, v_h__2_389_, v_h__3_390_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run_match__3_splitter___boxed(lean_object* v_00_u03b1_392_, lean_object* v_motive_393_, lean_object* v_x_394_, lean_object* v_x_395_, lean_object* v_h__1_396_, lean_object* v_h__2_397_, lean_object* v_h__3_398_){
_start:
{
lean_object* v_res_399_; 
v_res_399_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run_match__3_splitter(v_00_u03b1_392_, v_motive_393_, v_x_394_, v_x_395_, v_h__1_396_, v_h__2_397_, v_h__3_398_);
lean_dec(v_x_394_);
return v_res_399_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run_match__1_splitter___redArg(lean_object* v_x_400_, lean_object* v_h__1_401_){
_start:
{
lean_object* v_fst_402_; lean_object* v_snd_403_; lean_object* v___x_404_; 
v_fst_402_ = lean_ctor_get(v_x_400_, 0);
lean_inc(v_fst_402_);
v_snd_403_ = lean_ctor_get(v_x_400_, 1);
lean_inc(v_snd_403_);
lean_dec_ref(v_x_400_);
v___x_404_ = lean_apply_2(v_h__1_401_, v_fst_402_, v_snd_403_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run_match__1_splitter(lean_object* v_00_u03b1_405_, lean_object* v_n_406_, lean_object* v_motive_407_, lean_object* v_x_408_, lean_object* v_h__1_409_){
_start:
{
lean_object* v___x_410_; 
v___x_410_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run_match__1_splitter___redArg(v_x_408_, v_h__1_409_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run_match__1_splitter___boxed(lean_object* v_00_u03b1_411_, lean_object* v_n_412_, lean_object* v_motive_413_, lean_object* v_x_414_, lean_object* v_h__1_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run_match__1_splitter(v_00_u03b1_411_, v_n_412_, v_motive_413_, v_x_414_, v_h__1_415_);
lean_dec(v_n_412_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_mergeSortTR___redArg(lean_object* v_l_417_, lean_object* v_le_418_){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_419_ = l_List_lengthTR___redArg(v_l_417_);
v___x_420_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run___redArg(v_le_418_, v___x_419_, v_l_417_);
lean_dec(v___x_419_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_mergeSortTR(lean_object* v_00_u03b1_421_, lean_object* v_l_422_, lean_object* v_le_423_){
_start:
{
lean_object* v___x_424_; 
v___x_424_ = l_List_MergeSort_Internal_mergeSortTR___redArg(v_l_422_, v_le_423_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_splitRevInTwo___redArg(lean_object* v_n_425_, lean_object* v_l_426_){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v_r_430_; lean_object* v_fst_431_; lean_object* v_snd_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_439_; 
v___x_427_ = lean_unsigned_to_nat(1u);
v___x_428_ = lean_nat_add(v_n_425_, v___x_427_);
v___x_429_ = lean_nat_shiftr(v___x_428_, v___x_427_);
lean_dec(v___x_428_);
v_r_430_ = l_List_MergeSort_Internal_splitRevAt___redArg(v___x_429_, v_l_426_);
v_fst_431_ = lean_ctor_get(v_r_430_, 0);
v_snd_432_ = lean_ctor_get(v_r_430_, 1);
v_isSharedCheck_439_ = !lean_is_exclusive(v_r_430_);
if (v_isSharedCheck_439_ == 0)
{
v___x_434_ = v_r_430_;
v_isShared_435_ = v_isSharedCheck_439_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_snd_432_);
lean_inc(v_fst_431_);
lean_dec(v_r_430_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_439_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_437_; 
if (v_isShared_435_ == 0)
{
v___x_437_ = v___x_434_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v_fst_431_);
lean_ctor_set(v_reuseFailAlloc_438_, 1, v_snd_432_);
v___x_437_ = v_reuseFailAlloc_438_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
return v___x_437_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_splitRevInTwo___redArg___boxed(lean_object* v_n_440_, lean_object* v_l_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l_List_MergeSort_Internal_splitRevInTwo___redArg(v_n_440_, v_l_441_);
lean_dec(v_n_440_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_splitRevInTwo(lean_object* v_00_u03b1_443_, lean_object* v_n_444_, lean_object* v_l_445_){
_start:
{
lean_object* v___x_446_; 
v___x_446_ = l_List_MergeSort_Internal_splitRevInTwo___redArg(v_n_444_, v_l_445_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_splitRevInTwo___boxed(lean_object* v_00_u03b1_447_, lean_object* v_n_448_, lean_object* v_l_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l_List_MergeSort_Internal_splitRevInTwo(v_00_u03b1_447_, v_n_448_, v_l_449_);
lean_dec(v_n_448_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_splitRevInTwo_x27___redArg(lean_object* v_n_451_, lean_object* v_l_452_){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v_r_455_; lean_object* v_fst_456_; lean_object* v_snd_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_464_; 
v___x_453_ = lean_unsigned_to_nat(1u);
v___x_454_ = lean_nat_shiftr(v_n_451_, v___x_453_);
v_r_455_ = l_List_MergeSort_Internal_splitRevAt___redArg(v___x_454_, v_l_452_);
v_fst_456_ = lean_ctor_get(v_r_455_, 0);
v_snd_457_ = lean_ctor_get(v_r_455_, 1);
v_isSharedCheck_464_ = !lean_is_exclusive(v_r_455_);
if (v_isSharedCheck_464_ == 0)
{
v___x_459_ = v_r_455_;
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_snd_457_);
lean_inc(v_fst_456_);
lean_dec(v_r_455_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_462_; 
if (v_isShared_460_ == 0)
{
v___x_462_ = v___x_459_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_fst_456_);
lean_ctor_set(v_reuseFailAlloc_463_, 1, v_snd_457_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_splitRevInTwo_x27___redArg___boxed(lean_object* v_n_465_, lean_object* v_l_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_List_MergeSort_Internal_splitRevInTwo_x27___redArg(v_n_465_, v_l_466_);
lean_dec(v_n_465_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_splitRevInTwo_x27(lean_object* v_00_u03b1_468_, lean_object* v_n_469_, lean_object* v_l_470_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = l_List_MergeSort_Internal_splitRevInTwo_x27___redArg(v_n_469_, v_l_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_splitRevInTwo_x27___boxed(lean_object* v_00_u03b1_472_, lean_object* v_n_473_, lean_object* v_l_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l_List_MergeSort_Internal_splitRevInTwo_x27(v_00_u03b1_472_, v_n_473_, v_l_474_);
lean_dec(v_n_473_);
return v_res_475_;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR_u2082___auto__1(void){
_start:
{
lean_object* v___x_476_; 
v___x_476_ = lean_obj_once(&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__58, &l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__58_once, _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__58);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run___redArg(lean_object* v_le_477_, lean_object* v_n_478_, lean_object* v_a_479_){
_start:
{
lean_object* v_zero_480_; uint8_t v_isZero_481_; 
v_zero_480_ = lean_unsigned_to_nat(0u);
v_isZero_481_ = lean_nat_dec_eq(v_n_478_, v_zero_480_);
if (v_isZero_481_ == 1)
{
lean_dec_ref(v_le_477_);
return v_a_479_;
}
else
{
lean_object* v_one_482_; lean_object* v_n_483_; uint8_t v_isZero_484_; 
v_one_482_ = lean_unsigned_to_nat(1u);
v_n_483_ = lean_nat_sub(v_n_478_, v_one_482_);
v_isZero_484_ = lean_nat_dec_eq(v_n_483_, v_zero_480_);
if (v_isZero_484_ == 1)
{
lean_dec(v_n_483_);
lean_dec_ref(v_le_477_);
return v_a_479_;
}
else
{
lean_object* v_n_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v_fst_489_; lean_object* v_snd_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
v_n_485_ = lean_nat_sub(v_n_483_, v_one_482_);
lean_dec(v_n_483_);
v___x_486_ = lean_unsigned_to_nat(2u);
v___x_487_ = lean_nat_add(v_n_485_, v___x_486_);
lean_dec(v_n_485_);
v___x_488_ = l_List_MergeSort_Internal_splitRevInTwo___redArg(v___x_487_, v_a_479_);
v_fst_489_ = lean_ctor_get(v___x_488_, 0);
lean_inc(v_fst_489_);
v_snd_490_ = lean_ctor_get(v___x_488_, 1);
lean_inc(v_snd_490_);
lean_dec_ref(v___x_488_);
v___x_491_ = lean_nat_add(v___x_487_, v_one_482_);
v___x_492_ = lean_nat_shiftr(v___x_491_, v_one_482_);
lean_dec(v___x_491_);
lean_inc_ref(v_le_477_);
v___x_493_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run_x27___redArg(v_le_477_, v___x_492_, v_fst_489_);
lean_dec(v___x_492_);
v___x_494_ = lean_nat_shiftr(v___x_487_, v_one_482_);
lean_dec(v___x_487_);
lean_inc_ref(v_le_477_);
v___x_495_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run___redArg(v_le_477_, v___x_494_, v_snd_490_);
lean_dec(v___x_494_);
v___x_496_ = l_List_MergeSort_Internal_mergeTR___redArg(v___x_493_, v___x_495_, v_le_477_);
return v___x_496_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run_x27___redArg(lean_object* v_le_497_, lean_object* v_n_498_, lean_object* v_a_499_){
_start:
{
lean_object* v_zero_500_; uint8_t v_isZero_501_; 
v_zero_500_ = lean_unsigned_to_nat(0u);
v_isZero_501_ = lean_nat_dec_eq(v_n_498_, v_zero_500_);
if (v_isZero_501_ == 1)
{
lean_dec_ref(v_le_497_);
return v_a_499_;
}
else
{
lean_object* v_one_502_; lean_object* v_n_503_; uint8_t v_isZero_504_; 
v_one_502_ = lean_unsigned_to_nat(1u);
v_n_503_ = lean_nat_sub(v_n_498_, v_one_502_);
v_isZero_504_ = lean_nat_dec_eq(v_n_503_, v_zero_500_);
if (v_isZero_504_ == 1)
{
lean_dec(v_n_503_);
lean_dec_ref(v_le_497_);
return v_a_499_;
}
else
{
lean_object* v_n_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v_fst_509_; lean_object* v_snd_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v_n_505_ = lean_nat_sub(v_n_503_, v_one_502_);
lean_dec(v_n_503_);
v___x_506_ = lean_unsigned_to_nat(2u);
v___x_507_ = lean_nat_add(v_n_505_, v___x_506_);
lean_dec(v_n_505_);
v___x_508_ = l_List_MergeSort_Internal_splitRevInTwo_x27___redArg(v___x_507_, v_a_499_);
v_fst_509_ = lean_ctor_get(v___x_508_, 0);
lean_inc(v_fst_509_);
v_snd_510_ = lean_ctor_get(v___x_508_, 1);
lean_inc(v_snd_510_);
lean_dec_ref(v___x_508_);
v___x_511_ = lean_nat_add(v___x_507_, v_one_502_);
v___x_512_ = lean_nat_shiftr(v___x_511_, v_one_502_);
lean_dec(v___x_511_);
lean_inc_ref(v_le_497_);
v___x_513_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run_x27___redArg(v_le_497_, v___x_512_, v_snd_510_);
lean_dec(v___x_512_);
v___x_514_ = lean_nat_shiftr(v___x_507_, v_one_502_);
lean_dec(v___x_507_);
lean_inc_ref(v_le_497_);
v___x_515_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run___redArg(v_le_497_, v___x_514_, v_fst_509_);
lean_dec(v___x_514_);
v___x_516_ = l_List_MergeSort_Internal_mergeTR___redArg(v___x_513_, v___x_515_, v_le_497_);
return v___x_516_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run_x27___redArg___boxed(lean_object* v_le_517_, lean_object* v_n_518_, lean_object* v_a_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run_x27___redArg(v_le_517_, v_n_518_, v_a_519_);
lean_dec(v_n_518_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run___redArg___boxed(lean_object* v_le_521_, lean_object* v_n_522_, lean_object* v_a_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run___redArg(v_le_521_, v_n_522_, v_a_523_);
lean_dec(v_n_522_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run(lean_object* v_00_u03b1_525_, lean_object* v_le_526_, lean_object* v_n_527_, lean_object* v_a_528_){
_start:
{
lean_object* v___x_529_; 
v___x_529_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run___redArg(v_le_526_, v_n_527_, v_a_528_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run___boxed(lean_object* v_00_u03b1_530_, lean_object* v_le_531_, lean_object* v_n_532_, lean_object* v_a_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run(v_00_u03b1_530_, v_le_531_, v_n_532_, v_a_533_);
lean_dec(v_n_532_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run_x27(lean_object* v_00_u03b1_535_, lean_object* v_le_536_, lean_object* v_n_537_, lean_object* v_a_538_){
_start:
{
lean_object* v___x_539_; 
v___x_539_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run_x27___redArg(v_le_536_, v_n_537_, v_a_538_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run_x27___boxed(lean_object* v_00_u03b1_540_, lean_object* v_le_541_, lean_object* v_n_542_, lean_object* v_a_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run_x27(v_00_u03b1_540_, v_le_541_, v_n_542_, v_a_543_);
lean_dec(v_n_542_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run_x27_match__1_splitter___redArg(lean_object* v_x_545_, lean_object* v_h__1_546_){
_start:
{
lean_object* v_fst_547_; lean_object* v_snd_548_; lean_object* v___x_549_; 
v_fst_547_ = lean_ctor_get(v_x_545_, 0);
lean_inc(v_fst_547_);
v_snd_548_ = lean_ctor_get(v_x_545_, 1);
lean_inc(v_snd_548_);
lean_dec_ref(v_x_545_);
v___x_549_ = lean_apply_2(v_h__1_546_, v_fst_547_, v_snd_548_);
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run_x27_match__1_splitter(lean_object* v_00_u03b1_550_, lean_object* v_n_551_, lean_object* v_motive_552_, lean_object* v_x_553_, lean_object* v_h__1_554_){
_start:
{
lean_object* v___x_555_; 
v___x_555_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run_x27_match__1_splitter___redArg(v_x_553_, v_h__1_554_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run_x27_match__1_splitter___boxed(lean_object* v_00_u03b1_556_, lean_object* v_n_557_, lean_object* v_motive_558_, lean_object* v_x_559_, lean_object* v_h__1_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run_x27_match__1_splitter(v_00_u03b1_556_, v_n_557_, v_motive_558_, v_x_559_, v_h__1_560_);
lean_dec(v_n_557_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_mergeSortTR_u2082___redArg(lean_object* v_l_562_, lean_object* v_le_563_){
_start:
{
lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_564_ = l_List_lengthTR___redArg(v_l_562_);
v___x_565_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run___redArg(v_le_563_, v___x_564_, v_l_562_);
lean_dec(v___x_564_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_mergeSortTR_u2082(lean_object* v_00_u03b1_566_, lean_object* v_l_567_, lean_object* v_le_568_){
_start:
{
lean_object* v___x_569_; 
v___x_569_ = l_List_MergeSort_Internal_mergeSortTR_u2082___redArg(v_l_567_, v_le_568_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_mergeSort_match__1_splitter___redArg(lean_object* v_x_570_, lean_object* v_x_571_, lean_object* v_h__1_572_, lean_object* v_h__2_573_, lean_object* v_h__3_574_){
_start:
{
if (lean_obj_tag(v_x_570_) == 0)
{
lean_object* v___x_575_; 
lean_dec(v_h__3_574_);
lean_dec(v_h__2_573_);
v___x_575_ = lean_apply_1(v_h__1_572_, v_x_571_);
return v___x_575_;
}
else
{
lean_object* v_tail_576_; 
lean_dec(v_h__1_572_);
v_tail_576_ = lean_ctor_get(v_x_570_, 1);
if (lean_obj_tag(v_tail_576_) == 0)
{
lean_object* v_head_577_; lean_object* v___x_578_; 
lean_dec(v_h__3_574_);
v_head_577_ = lean_ctor_get(v_x_570_, 0);
lean_inc(v_head_577_);
lean_dec_ref(v_x_570_);
v___x_578_ = lean_apply_2(v_h__2_573_, v_head_577_, v_x_571_);
return v___x_578_;
}
else
{
lean_object* v_head_579_; lean_object* v_head_580_; lean_object* v_tail_581_; lean_object* v___x_582_; 
lean_inc_ref(v_tail_576_);
lean_dec(v_h__2_573_);
v_head_579_ = lean_ctor_get(v_x_570_, 0);
lean_inc(v_head_579_);
lean_dec_ref(v_x_570_);
v_head_580_ = lean_ctor_get(v_tail_576_, 0);
lean_inc(v_head_580_);
v_tail_581_ = lean_ctor_get(v_tail_576_, 1);
lean_inc(v_tail_581_);
lean_dec_ref(v_tail_576_);
v___x_582_ = lean_apply_4(v_h__3_574_, v_head_579_, v_head_580_, v_tail_581_, v_x_571_);
return v___x_582_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_mergeSort_match__1_splitter(lean_object* v_00_u03b1_583_, lean_object* v_motive_584_, lean_object* v_x_585_, lean_object* v_x_586_, lean_object* v_h__1_587_, lean_object* v_h__2_588_, lean_object* v_h__3_589_){
_start:
{
lean_object* v___x_590_; 
v___x_590_ = l___private_Init_Data_List_Sort_Impl_0__List_mergeSort_match__1_splitter___redArg(v_x_585_, v_x_586_, v_h__1_587_, v_h__2_588_, v_h__3_589_);
return v___x_590_;
}
}
lean_object* runtime_initialize_Init_Data_List_Sort_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Sort_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Sort_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Linear(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_List_Sort_Impl(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_List_Sort_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Sort_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Sort_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_List_Sort_Impl(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_List_MergeSort_Internal_mergeSortTR___auto__1 = _init_l_List_MergeSort_Internal_mergeSortTR___auto__1();
lean_mark_persistent(l_List_MergeSort_Internal_mergeSortTR___auto__1);
l_List_MergeSort_Internal_mergeSortTR_u2082___auto__1 = _init_l_List_MergeSort_Internal_mergeSortTR_u2082___auto__1();
lean_mark_persistent(l_List_MergeSort_Internal_mergeSortTR_u2082___auto__1);
return lean_io_result_mk_ok(lean_box(0));
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
res = runtime_initialize_Init_Data_List_Sort_Impl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_List_Sort_Impl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_List_Sort_Impl(builtin);
}
#ifdef __cplusplus
}
#endif

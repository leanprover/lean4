// Lean compiler output
// Module: Init.Data.List.Sort.Impl
// Imports: import all Init.Data.List.Sort.Basic public import Init.Data.List.Sort.Basic import Init.Data.List.Sort.Lemmas import Init.Data.Nat.Internal.Linear
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
static const lean_ctor_object l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__21_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__22 = (const lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__22_value;
static const lean_ctor_object l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(247, 80, 99, 121, 74, 33, 203, 108)}};
static const lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__23 = (const lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__23_value;
static const lean_ctor_object l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 3}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__22_value),((lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__23_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__24 = (const lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__24_value;
static lean_once_cell_t l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__25;
static const lean_string_object l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "b"};
static const lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__26 = (const lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__26_value;
static const lean_ctor_object l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__26_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__27 = (const lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__27_value;
static const lean_ctor_object l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__26_value),LEAN_SCALAR_PTR_LITERAL(47, 22, 244, 233, 226, 169, 241, 142)}};
static const lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__28 = (const lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__28_value;
static const lean_ctor_object l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 3}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__27_value),((lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__28_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__29 = (const lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__29_value;
static lean_once_cell_t l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__30;
static lean_once_cell_t l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__31;
static lean_once_cell_t l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__32;
static const lean_ctor_object l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__9_value),((lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__5_value)}};
static const lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__33 = (const lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__33_value;
static lean_once_cell_t l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__34;
static const lean_string_object l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__35 = (const lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__35_value;
static lean_once_cell_t l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__36;
static lean_once_cell_t l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__37;
static const lean_string_object l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 7, .m_data = "term_≤_"};
static const lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__38 = (const lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__38_value;
static const lean_ctor_object l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__38_value),LEAN_SCALAR_PTR_LITERAL(111, 3, 61, 112, 38, 138, 106, 121)}};
static const lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__39 = (const lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__39_value;
static const lean_string_object l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "≤"};
static const lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__40 = (const lean_object*)&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__40_value;
static lean_once_cell_t l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__41;
static lean_once_cell_t l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__42;
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
lean_dec_ref_known(v_x_39_, 2);
v_head_49_ = lean_ctor_get(v_x_40_, 0);
lean_inc(v_head_49_);
v_tail_50_ = lean_ctor_get(v_x_40_, 1);
lean_inc(v_tail_50_);
lean_dec_ref_known(v_x_40_, 2);
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
lean_dec_ref_known(v_x_54_, 2);
v_head_64_ = lean_ctor_get(v_x_55_, 0);
lean_inc(v_head_64_);
v_tail_65_ = lean_ctor_get(v_x_55_, 1);
lean_inc(v_tail_65_);
lean_dec_ref_known(v_x_55_, 2);
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
lean_dec_ref_known(v_xs_77_, 2);
v_head_86_ = lean_ctor_get(v_ys_78_, 0);
lean_inc(v_head_86_);
v_tail_87_ = lean_ctor_get(v_ys_78_, 1);
lean_inc(v_tail_87_);
lean_dec_ref_known(v_ys_78_, 2);
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
lean_dec_ref_known(v_xs_91_, 2);
v_head_100_ = lean_ctor_get(v_ys_92_, 0);
lean_inc(v_head_100_);
v_tail_101_ = lean_ctor_get(v_ys_92_, 1);
lean_inc(v_tail_101_);
lean_dec_ref_known(v_ys_92_, 2);
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
lean_dec_ref_known(v_x_137_, 2);
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
lean_dec_ref_known(v_x_153_, 2);
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
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__25(void){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_228_ = ((lean_object*)(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__24));
v___x_229_ = ((lean_object*)(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__5));
v___x_230_ = lean_array_push(v___x_229_, v___x_228_);
return v___x_230_;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__30(void){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_243_ = ((lean_object*)(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__29));
v___x_244_ = lean_obj_once(&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__25, &l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__25_once, _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__25);
v___x_245_ = lean_array_push(v___x_244_, v___x_243_);
return v___x_245_;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__31(void){
_start:
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_246_ = lean_obj_once(&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__30, &l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__30_once, _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__30);
v___x_247_ = ((lean_object*)(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__9));
v___x_248_ = lean_box(2);
v___x_249_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_249_, 0, v___x_248_);
lean_ctor_set(v___x_249_, 1, v___x_247_);
lean_ctor_set(v___x_249_, 2, v___x_246_);
return v___x_249_;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__32(void){
_start:
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_250_ = lean_obj_once(&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__31, &l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__31_once, _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__31);
v___x_251_ = ((lean_object*)(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__5));
v___x_252_ = lean_array_push(v___x_251_, v___x_250_);
return v___x_252_;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__34(void){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_257_ = ((lean_object*)(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__33));
v___x_258_ = lean_obj_once(&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__32, &l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__32_once, _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__32);
v___x_259_ = lean_array_push(v___x_258_, v___x_257_);
return v___x_259_;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__36(void){
_start:
{
lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_261_ = ((lean_object*)(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__35));
v___x_262_ = l_Lean_mkAtom(v___x_261_);
return v___x_262_;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__37(void){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_263_ = lean_obj_once(&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__36, &l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__36_once, _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__36);
v___x_264_ = lean_obj_once(&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__34, &l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__34_once, _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__34);
v___x_265_ = lean_array_push(v___x_264_, v___x_263_);
return v___x_265_;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__41(void){
_start:
{
lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_270_ = ((lean_object*)(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__40));
v___x_271_ = l_Lean_mkAtom(v___x_270_);
return v___x_271_;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__42(void){
_start:
{
lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_272_ = lean_obj_once(&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__41, &l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__41_once, _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__41);
v___x_273_ = lean_obj_once(&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__25, &l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__25_once, _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__25);
v___x_274_ = lean_array_push(v___x_273_, v___x_272_);
return v___x_274_;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__43(void){
_start:
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_275_ = ((lean_object*)(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__29));
v___x_276_ = lean_obj_once(&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__42, &l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__42_once, _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__42);
v___x_277_ = lean_array_push(v___x_276_, v___x_275_);
return v___x_277_;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__44(void){
_start:
{
lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_278_ = lean_obj_once(&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__43, &l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__43_once, _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__43);
v___x_279_ = ((lean_object*)(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__39));
v___x_280_ = lean_box(2);
v___x_281_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_281_, 0, v___x_280_);
lean_ctor_set(v___x_281_, 1, v___x_279_);
lean_ctor_set(v___x_281_, 2, v___x_278_);
return v___x_281_;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__45(void){
_start:
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_282_ = lean_obj_once(&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__44, &l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__44_once, _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__44);
v___x_283_ = lean_obj_once(&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__37, &l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__37_once, _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__37);
v___x_284_ = lean_array_push(v___x_283_, v___x_282_);
return v___x_284_;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__46(void){
_start:
{
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_285_ = lean_obj_once(&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__45, &l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__45_once, _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__45);
v___x_286_ = ((lean_object*)(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__20));
v___x_287_ = lean_box(2);
v___x_288_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_288_, 0, v___x_287_);
lean_ctor_set(v___x_288_, 1, v___x_286_);
lean_ctor_set(v___x_288_, 2, v___x_285_);
return v___x_288_;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__47(void){
_start:
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_289_ = lean_obj_once(&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__46, &l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__46_once, _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__46);
v___x_290_ = lean_obj_once(&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__18, &l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__18_once, _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__18);
v___x_291_ = lean_array_push(v___x_290_, v___x_289_);
return v___x_291_;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__48(void){
_start:
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_292_ = lean_obj_once(&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__47, &l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__47_once, _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__47);
v___x_293_ = ((lean_object*)(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__16));
v___x_294_ = lean_box(2);
v___x_295_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_295_, 0, v___x_294_);
lean_ctor_set(v___x_295_, 1, v___x_293_);
lean_ctor_set(v___x_295_, 2, v___x_292_);
return v___x_295_;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__49(void){
_start:
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_296_ = lean_obj_once(&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__48, &l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__48_once, _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__48);
v___x_297_ = lean_obj_once(&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__13, &l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__13_once, _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__13);
v___x_298_ = lean_array_push(v___x_297_, v___x_296_);
return v___x_298_;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__50(void){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_299_ = lean_obj_once(&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__49, &l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__49_once, _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__49);
v___x_300_ = ((lean_object*)(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__11));
v___x_301_ = lean_box(2);
v___x_302_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_302_, 0, v___x_301_);
lean_ctor_set(v___x_302_, 1, v___x_300_);
lean_ctor_set(v___x_302_, 2, v___x_299_);
return v___x_302_;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__51(void){
_start:
{
lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_303_ = lean_obj_once(&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__50, &l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__50_once, _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__50);
v___x_304_ = ((lean_object*)(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__5));
v___x_305_ = lean_array_push(v___x_304_, v___x_303_);
return v___x_305_;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__52(void){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_306_ = lean_obj_once(&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__51, &l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__51_once, _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__51);
v___x_307_ = ((lean_object*)(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__9));
v___x_308_ = lean_box(2);
v___x_309_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_309_, 0, v___x_308_);
lean_ctor_set(v___x_309_, 1, v___x_307_);
lean_ctor_set(v___x_309_, 2, v___x_306_);
return v___x_309_;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__53(void){
_start:
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_310_ = lean_obj_once(&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__52, &l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__52_once, _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__52);
v___x_311_ = ((lean_object*)(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__5));
v___x_312_ = lean_array_push(v___x_311_, v___x_310_);
return v___x_312_;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__54(void){
_start:
{
lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_313_ = lean_obj_once(&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__53, &l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__53_once, _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__53);
v___x_314_ = ((lean_object*)(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__7));
v___x_315_ = lean_box(2);
v___x_316_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_316_, 0, v___x_315_);
lean_ctor_set(v___x_316_, 1, v___x_314_);
lean_ctor_set(v___x_316_, 2, v___x_313_);
return v___x_316_;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__55(void){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_317_ = lean_obj_once(&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__54, &l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__54_once, _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__54);
v___x_318_ = ((lean_object*)(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__5));
v___x_319_ = lean_array_push(v___x_318_, v___x_317_);
return v___x_319_;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__56(void){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_320_ = lean_obj_once(&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__55, &l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__55_once, _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__55);
v___x_321_ = ((lean_object*)(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__4));
v___x_322_ = lean_box(2);
v___x_323_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_323_, 0, v___x_322_);
lean_ctor_set(v___x_323_, 1, v___x_321_);
lean_ctor_set(v___x_323_, 2, v___x_320_);
return v___x_323_;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR___auto__1(void){
_start:
{
lean_object* v___x_324_; 
v___x_324_ = lean_obj_once(&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__56, &l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__56_once, _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__56);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run___redArg(lean_object* v_le_325_, lean_object* v_n_326_, lean_object* v_a_327_){
_start:
{
lean_object* v_zero_328_; uint8_t v_isZero_329_; 
v_zero_328_ = lean_unsigned_to_nat(0u);
v_isZero_329_ = lean_nat_dec_eq(v_n_326_, v_zero_328_);
if (v_isZero_329_ == 1)
{
lean_dec_ref(v_le_325_);
return v_a_327_;
}
else
{
lean_object* v_one_330_; lean_object* v_n_331_; uint8_t v_isZero_332_; 
v_one_330_ = lean_unsigned_to_nat(1u);
v_n_331_ = lean_nat_sub(v_n_326_, v_one_330_);
v_isZero_332_ = lean_nat_dec_eq(v_n_331_, v_zero_328_);
if (v_isZero_332_ == 1)
{
lean_dec(v_n_331_);
lean_dec_ref(v_le_325_);
return v_a_327_;
}
else
{
lean_object* v_n_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v_fst_337_; lean_object* v_snd_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
v_n_333_ = lean_nat_sub(v_n_331_, v_one_330_);
lean_dec(v_n_331_);
v___x_334_ = lean_unsigned_to_nat(2u);
v___x_335_ = lean_nat_add(v_n_333_, v___x_334_);
lean_dec(v_n_333_);
v___x_336_ = l_List_MergeSort_Internal_splitInTwo___redArg(v___x_335_, v_a_327_);
v_fst_337_ = lean_ctor_get(v___x_336_, 0);
lean_inc(v_fst_337_);
v_snd_338_ = lean_ctor_get(v___x_336_, 1);
lean_inc(v_snd_338_);
lean_dec_ref(v___x_336_);
v___x_339_ = lean_nat_add(v___x_335_, v_one_330_);
v___x_340_ = lean_nat_shiftr(v___x_339_, v_one_330_);
lean_dec(v___x_339_);
lean_inc_ref_n(v_le_325_, 2);
v___x_341_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run___redArg(v_le_325_, v___x_340_, v_fst_337_);
lean_dec(v___x_340_);
v___x_342_ = lean_nat_shiftr(v___x_335_, v_one_330_);
lean_dec(v___x_335_);
v___x_343_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run___redArg(v_le_325_, v___x_342_, v_snd_338_);
lean_dec(v___x_342_);
v___x_344_ = l_List_MergeSort_Internal_mergeTR___redArg(v___x_341_, v___x_343_, v_le_325_);
return v___x_344_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run___redArg___boxed(lean_object* v_le_345_, lean_object* v_n_346_, lean_object* v_a_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run___redArg(v_le_345_, v_n_346_, v_a_347_);
lean_dec(v_n_346_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run(lean_object* v_00_u03b1_349_, lean_object* v_le_350_, lean_object* v_n_351_, lean_object* v_a_352_){
_start:
{
lean_object* v___x_353_; 
v___x_353_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run___redArg(v_le_350_, v_n_351_, v_a_352_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run___boxed(lean_object* v_00_u03b1_354_, lean_object* v_le_355_, lean_object* v_n_356_, lean_object* v_a_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run(v_00_u03b1_354_, v_le_355_, v_n_356_, v_a_357_);
lean_dec(v_n_356_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run_match__3_splitter___redArg(lean_object* v_x_359_, lean_object* v_x_360_, lean_object* v_h__1_361_, lean_object* v_h__2_362_, lean_object* v_h__3_363_){
_start:
{
lean_object* v_zero_364_; uint8_t v_isZero_365_; 
v_zero_364_ = lean_unsigned_to_nat(0u);
v_isZero_365_ = lean_nat_dec_eq(v_x_359_, v_zero_364_);
if (v_isZero_365_ == 1)
{
lean_object* v___x_366_; 
lean_dec(v_h__3_363_);
lean_dec(v_h__2_362_);
lean_dec(v_x_360_);
v___x_366_ = lean_apply_1(v_h__1_361_, lean_box(0));
return v___x_366_;
}
else
{
lean_object* v_one_367_; lean_object* v_n_368_; uint8_t v_isZero_369_; 
lean_dec(v_h__1_361_);
v_one_367_ = lean_unsigned_to_nat(1u);
v_n_368_ = lean_nat_sub(v_x_359_, v_one_367_);
v_isZero_369_ = lean_nat_dec_eq(v_n_368_, v_zero_364_);
if (v_isZero_369_ == 1)
{
lean_object* v_head_370_; lean_object* v___x_371_; 
lean_dec(v_n_368_);
lean_dec(v_h__3_363_);
v_head_370_ = lean_ctor_get(v_x_360_, 0);
lean_inc(v_head_370_);
lean_dec(v_x_360_);
v___x_371_ = lean_apply_2(v_h__2_362_, v_head_370_, lean_box(0));
return v___x_371_;
}
else
{
lean_object* v_n_372_; lean_object* v___x_373_; 
lean_dec(v_h__2_362_);
v_n_372_ = lean_nat_sub(v_n_368_, v_one_367_);
lean_dec(v_n_368_);
v___x_373_ = lean_apply_2(v_h__3_363_, v_n_372_, v_x_360_);
return v___x_373_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run_match__3_splitter___redArg___boxed(lean_object* v_x_374_, lean_object* v_x_375_, lean_object* v_h__1_376_, lean_object* v_h__2_377_, lean_object* v_h__3_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run_match__3_splitter___redArg(v_x_374_, v_x_375_, v_h__1_376_, v_h__2_377_, v_h__3_378_);
lean_dec(v_x_374_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run_match__3_splitter(lean_object* v_00_u03b1_380_, lean_object* v_motive_381_, lean_object* v_x_382_, lean_object* v_x_383_, lean_object* v_h__1_384_, lean_object* v_h__2_385_, lean_object* v_h__3_386_){
_start:
{
lean_object* v_zero_387_; uint8_t v_isZero_388_; 
v_zero_387_ = lean_unsigned_to_nat(0u);
v_isZero_388_ = lean_nat_dec_eq(v_x_382_, v_zero_387_);
if (v_isZero_388_ == 1)
{
lean_object* v___x_389_; 
lean_dec(v_h__3_386_);
lean_dec(v_h__2_385_);
lean_dec(v_x_383_);
v___x_389_ = lean_apply_1(v_h__1_384_, lean_box(0));
return v___x_389_;
}
else
{
lean_object* v_one_390_; lean_object* v_n_391_; uint8_t v_isZero_392_; 
lean_dec(v_h__1_384_);
v_one_390_ = lean_unsigned_to_nat(1u);
v_n_391_ = lean_nat_sub(v_x_382_, v_one_390_);
v_isZero_392_ = lean_nat_dec_eq(v_n_391_, v_zero_387_);
if (v_isZero_392_ == 1)
{
lean_object* v_head_393_; lean_object* v___x_394_; 
lean_dec(v_n_391_);
lean_dec(v_h__3_386_);
v_head_393_ = lean_ctor_get(v_x_383_, 0);
lean_inc(v_head_393_);
lean_dec(v_x_383_);
v___x_394_ = lean_apply_2(v_h__2_385_, v_head_393_, lean_box(0));
return v___x_394_;
}
else
{
lean_object* v_n_395_; lean_object* v___x_396_; 
lean_dec(v_h__2_385_);
v_n_395_ = lean_nat_sub(v_n_391_, v_one_390_);
lean_dec(v_n_391_);
v___x_396_ = lean_apply_2(v_h__3_386_, v_n_395_, v_x_383_);
return v___x_396_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run_match__3_splitter___boxed(lean_object* v_00_u03b1_397_, lean_object* v_motive_398_, lean_object* v_x_399_, lean_object* v_x_400_, lean_object* v_h__1_401_, lean_object* v_h__2_402_, lean_object* v_h__3_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run_match__3_splitter(v_00_u03b1_397_, v_motive_398_, v_x_399_, v_x_400_, v_h__1_401_, v_h__2_402_, v_h__3_403_);
lean_dec(v_x_399_);
return v_res_404_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run_match__1_splitter___redArg(lean_object* v_x_405_, lean_object* v_h__1_406_){
_start:
{
lean_object* v_fst_407_; lean_object* v_snd_408_; lean_object* v___x_409_; 
v_fst_407_ = lean_ctor_get(v_x_405_, 0);
lean_inc(v_fst_407_);
v_snd_408_ = lean_ctor_get(v_x_405_, 1);
lean_inc(v_snd_408_);
lean_dec_ref(v_x_405_);
v___x_409_ = lean_apply_2(v_h__1_406_, v_fst_407_, v_snd_408_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run_match__1_splitter(lean_object* v_00_u03b1_410_, lean_object* v_n_411_, lean_object* v_motive_412_, lean_object* v_x_413_, lean_object* v_h__1_414_){
_start:
{
lean_object* v_fst_415_; lean_object* v_snd_416_; lean_object* v___x_417_; 
v_fst_415_ = lean_ctor_get(v_x_413_, 0);
lean_inc(v_fst_415_);
v_snd_416_ = lean_ctor_get(v_x_413_, 1);
lean_inc(v_snd_416_);
lean_dec_ref(v_x_413_);
v___x_417_ = lean_apply_2(v_h__1_414_, v_fst_415_, v_snd_416_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run_match__1_splitter___boxed(lean_object* v_00_u03b1_418_, lean_object* v_n_419_, lean_object* v_motive_420_, lean_object* v_x_421_, lean_object* v_h__1_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run_match__1_splitter(v_00_u03b1_418_, v_n_419_, v_motive_420_, v_x_421_, v_h__1_422_);
lean_dec(v_n_419_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_mergeSortTR___redArg(lean_object* v_l_424_, lean_object* v_le_425_){
_start:
{
lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_426_ = l_List_lengthTR___redArg(v_l_424_);
v___x_427_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run___redArg(v_le_425_, v___x_426_, v_l_424_);
lean_dec(v___x_426_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_mergeSortTR(lean_object* v_00_u03b1_428_, lean_object* v_l_429_, lean_object* v_le_430_){
_start:
{
lean_object* v___x_431_; 
v___x_431_ = l_List_MergeSort_Internal_mergeSortTR___redArg(v_l_429_, v_le_430_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_splitRevInTwo___redArg(lean_object* v_n_432_, lean_object* v_l_433_){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v_r_437_; lean_object* v_fst_438_; lean_object* v_snd_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_446_; 
v___x_434_ = lean_unsigned_to_nat(1u);
v___x_435_ = lean_nat_add(v_n_432_, v___x_434_);
v___x_436_ = lean_nat_shiftr(v___x_435_, v___x_434_);
lean_dec(v___x_435_);
v_r_437_ = l_List_MergeSort_Internal_splitRevAt___redArg(v___x_436_, v_l_433_);
v_fst_438_ = lean_ctor_get(v_r_437_, 0);
v_snd_439_ = lean_ctor_get(v_r_437_, 1);
v_isSharedCheck_446_ = !lean_is_exclusive(v_r_437_);
if (v_isSharedCheck_446_ == 0)
{
v___x_441_ = v_r_437_;
v_isShared_442_ = v_isSharedCheck_446_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_snd_439_);
lean_inc(v_fst_438_);
lean_dec(v_r_437_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_446_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_444_; 
if (v_isShared_442_ == 0)
{
v___x_444_ = v___x_441_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v_fst_438_);
lean_ctor_set(v_reuseFailAlloc_445_, 1, v_snd_439_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
return v___x_444_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_splitRevInTwo___redArg___boxed(lean_object* v_n_447_, lean_object* v_l_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l_List_MergeSort_Internal_splitRevInTwo___redArg(v_n_447_, v_l_448_);
lean_dec(v_n_447_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_splitRevInTwo(lean_object* v_00_u03b1_450_, lean_object* v_n_451_, lean_object* v_l_452_){
_start:
{
lean_object* v___x_453_; 
v___x_453_ = l_List_MergeSort_Internal_splitRevInTwo___redArg(v_n_451_, v_l_452_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_splitRevInTwo___boxed(lean_object* v_00_u03b1_454_, lean_object* v_n_455_, lean_object* v_l_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l_List_MergeSort_Internal_splitRevInTwo(v_00_u03b1_454_, v_n_455_, v_l_456_);
lean_dec(v_n_455_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_splitRevInTwo_x27___redArg(lean_object* v_n_458_, lean_object* v_l_459_){
_start:
{
lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v_r_462_; lean_object* v_fst_463_; lean_object* v_snd_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_471_; 
v___x_460_ = lean_unsigned_to_nat(1u);
v___x_461_ = lean_nat_shiftr(v_n_458_, v___x_460_);
v_r_462_ = l_List_MergeSort_Internal_splitRevAt___redArg(v___x_461_, v_l_459_);
v_fst_463_ = lean_ctor_get(v_r_462_, 0);
v_snd_464_ = lean_ctor_get(v_r_462_, 1);
v_isSharedCheck_471_ = !lean_is_exclusive(v_r_462_);
if (v_isSharedCheck_471_ == 0)
{
v___x_466_ = v_r_462_;
v_isShared_467_ = v_isSharedCheck_471_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_snd_464_);
lean_inc(v_fst_463_);
lean_dec(v_r_462_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_471_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
lean_object* v___x_469_; 
if (v_isShared_467_ == 0)
{
v___x_469_ = v___x_466_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v_fst_463_);
lean_ctor_set(v_reuseFailAlloc_470_, 1, v_snd_464_);
v___x_469_ = v_reuseFailAlloc_470_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
return v___x_469_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_splitRevInTwo_x27___redArg___boxed(lean_object* v_n_472_, lean_object* v_l_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l_List_MergeSort_Internal_splitRevInTwo_x27___redArg(v_n_472_, v_l_473_);
lean_dec(v_n_472_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_splitRevInTwo_x27(lean_object* v_00_u03b1_475_, lean_object* v_n_476_, lean_object* v_l_477_){
_start:
{
lean_object* v___x_478_; 
v___x_478_ = l_List_MergeSort_Internal_splitRevInTwo_x27___redArg(v_n_476_, v_l_477_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_splitRevInTwo_x27___boxed(lean_object* v_00_u03b1_479_, lean_object* v_n_480_, lean_object* v_l_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_List_MergeSort_Internal_splitRevInTwo_x27(v_00_u03b1_479_, v_n_480_, v_l_481_);
lean_dec(v_n_480_);
return v_res_482_;
}
}
static lean_object* _init_l_List_MergeSort_Internal_mergeSortTR_u2082___auto__1(void){
_start:
{
lean_object* v___x_483_; 
v___x_483_ = lean_obj_once(&l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__56, &l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__56_once, _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__56);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run___redArg(lean_object* v_le_484_, lean_object* v_n_485_, lean_object* v_a_486_){
_start:
{
lean_object* v_zero_487_; uint8_t v_isZero_488_; 
v_zero_487_ = lean_unsigned_to_nat(0u);
v_isZero_488_ = lean_nat_dec_eq(v_n_485_, v_zero_487_);
if (v_isZero_488_ == 1)
{
lean_dec_ref(v_le_484_);
return v_a_486_;
}
else
{
lean_object* v_one_489_; lean_object* v_n_490_; uint8_t v_isZero_491_; 
v_one_489_ = lean_unsigned_to_nat(1u);
v_n_490_ = lean_nat_sub(v_n_485_, v_one_489_);
v_isZero_491_ = lean_nat_dec_eq(v_n_490_, v_zero_487_);
if (v_isZero_491_ == 1)
{
lean_dec(v_n_490_);
lean_dec_ref(v_le_484_);
return v_a_486_;
}
else
{
lean_object* v_n_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v_fst_496_; lean_object* v_snd_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v_n_492_ = lean_nat_sub(v_n_490_, v_one_489_);
lean_dec(v_n_490_);
v___x_493_ = lean_unsigned_to_nat(2u);
v___x_494_ = lean_nat_add(v_n_492_, v___x_493_);
lean_dec(v_n_492_);
v___x_495_ = l_List_MergeSort_Internal_splitRevInTwo___redArg(v___x_494_, v_a_486_);
v_fst_496_ = lean_ctor_get(v___x_495_, 0);
lean_inc(v_fst_496_);
v_snd_497_ = lean_ctor_get(v___x_495_, 1);
lean_inc(v_snd_497_);
lean_dec_ref(v___x_495_);
v___x_498_ = lean_nat_add(v___x_494_, v_one_489_);
v___x_499_ = lean_nat_shiftr(v___x_498_, v_one_489_);
lean_dec(v___x_498_);
lean_inc_ref_n(v_le_484_, 2);
v___x_500_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run_x27___redArg(v_le_484_, v___x_499_, v_fst_496_);
lean_dec(v___x_499_);
v___x_501_ = lean_nat_shiftr(v___x_494_, v_one_489_);
lean_dec(v___x_494_);
v___x_502_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run___redArg(v_le_484_, v___x_501_, v_snd_497_);
lean_dec(v___x_501_);
v___x_503_ = l_List_MergeSort_Internal_mergeTR___redArg(v___x_500_, v___x_502_, v_le_484_);
return v___x_503_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run_x27___redArg(lean_object* v_le_504_, lean_object* v_n_505_, lean_object* v_a_506_){
_start:
{
lean_object* v_zero_507_; uint8_t v_isZero_508_; 
v_zero_507_ = lean_unsigned_to_nat(0u);
v_isZero_508_ = lean_nat_dec_eq(v_n_505_, v_zero_507_);
if (v_isZero_508_ == 1)
{
lean_dec_ref(v_le_504_);
return v_a_506_;
}
else
{
lean_object* v_one_509_; lean_object* v_n_510_; uint8_t v_isZero_511_; 
v_one_509_ = lean_unsigned_to_nat(1u);
v_n_510_ = lean_nat_sub(v_n_505_, v_one_509_);
v_isZero_511_ = lean_nat_dec_eq(v_n_510_, v_zero_507_);
if (v_isZero_511_ == 1)
{
lean_dec(v_n_510_);
lean_dec_ref(v_le_504_);
return v_a_506_;
}
else
{
lean_object* v_n_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v_fst_516_; lean_object* v_snd_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
v_n_512_ = lean_nat_sub(v_n_510_, v_one_509_);
lean_dec(v_n_510_);
v___x_513_ = lean_unsigned_to_nat(2u);
v___x_514_ = lean_nat_add(v_n_512_, v___x_513_);
lean_dec(v_n_512_);
v___x_515_ = l_List_MergeSort_Internal_splitRevInTwo_x27___redArg(v___x_514_, v_a_506_);
v_fst_516_ = lean_ctor_get(v___x_515_, 0);
lean_inc(v_fst_516_);
v_snd_517_ = lean_ctor_get(v___x_515_, 1);
lean_inc(v_snd_517_);
lean_dec_ref(v___x_515_);
v___x_518_ = lean_nat_add(v___x_514_, v_one_509_);
v___x_519_ = lean_nat_shiftr(v___x_518_, v_one_509_);
lean_dec(v___x_518_);
lean_inc_ref_n(v_le_504_, 2);
v___x_520_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run_x27___redArg(v_le_504_, v___x_519_, v_snd_517_);
lean_dec(v___x_519_);
v___x_521_ = lean_nat_shiftr(v___x_514_, v_one_509_);
lean_dec(v___x_514_);
v___x_522_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run___redArg(v_le_504_, v___x_521_, v_fst_516_);
lean_dec(v___x_521_);
v___x_523_ = l_List_MergeSort_Internal_mergeTR___redArg(v___x_520_, v___x_522_, v_le_504_);
return v___x_523_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run_x27___redArg___boxed(lean_object* v_le_524_, lean_object* v_n_525_, lean_object* v_a_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run_x27___redArg(v_le_524_, v_n_525_, v_a_526_);
lean_dec(v_n_525_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run___redArg___boxed(lean_object* v_le_528_, lean_object* v_n_529_, lean_object* v_a_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run___redArg(v_le_528_, v_n_529_, v_a_530_);
lean_dec(v_n_529_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run(lean_object* v_00_u03b1_532_, lean_object* v_le_533_, lean_object* v_n_534_, lean_object* v_a_535_){
_start:
{
lean_object* v___x_536_; 
v___x_536_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run___redArg(v_le_533_, v_n_534_, v_a_535_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run___boxed(lean_object* v_00_u03b1_537_, lean_object* v_le_538_, lean_object* v_n_539_, lean_object* v_a_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run(v_00_u03b1_537_, v_le_538_, v_n_539_, v_a_540_);
lean_dec(v_n_539_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run_x27(lean_object* v_00_u03b1_542_, lean_object* v_le_543_, lean_object* v_n_544_, lean_object* v_a_545_){
_start:
{
lean_object* v___x_546_; 
v___x_546_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run_x27___redArg(v_le_543_, v_n_544_, v_a_545_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run_x27___boxed(lean_object* v_00_u03b1_547_, lean_object* v_le_548_, lean_object* v_n_549_, lean_object* v_a_550_){
_start:
{
lean_object* v_res_551_; 
v_res_551_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run_x27(v_00_u03b1_547_, v_le_548_, v_n_549_, v_a_550_);
lean_dec(v_n_549_);
return v_res_551_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run_x27_match__1_splitter___redArg(lean_object* v_x_552_, lean_object* v_h__1_553_){
_start:
{
lean_object* v_fst_554_; lean_object* v_snd_555_; lean_object* v___x_556_; 
v_fst_554_ = lean_ctor_get(v_x_552_, 0);
lean_inc(v_fst_554_);
v_snd_555_ = lean_ctor_get(v_x_552_, 1);
lean_inc(v_snd_555_);
lean_dec_ref(v_x_552_);
v___x_556_ = lean_apply_2(v_h__1_553_, v_fst_554_, v_snd_555_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run_x27_match__1_splitter(lean_object* v_00_u03b1_557_, lean_object* v_n_558_, lean_object* v_motive_559_, lean_object* v_x_560_, lean_object* v_h__1_561_){
_start:
{
lean_object* v_fst_562_; lean_object* v_snd_563_; lean_object* v___x_564_; 
v_fst_562_ = lean_ctor_get(v_x_560_, 0);
lean_inc(v_fst_562_);
v_snd_563_ = lean_ctor_get(v_x_560_, 1);
lean_inc(v_snd_563_);
lean_dec_ref(v_x_560_);
v___x_564_ = lean_apply_2(v_h__1_561_, v_fst_562_, v_snd_563_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run_x27_match__1_splitter___boxed(lean_object* v_00_u03b1_565_, lean_object* v_n_566_, lean_object* v_motive_567_, lean_object* v_x_568_, lean_object* v_h__1_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run_x27_match__1_splitter(v_00_u03b1_565_, v_n_566_, v_motive_567_, v_x_568_, v_h__1_569_);
lean_dec(v_n_566_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_mergeSortTR_u2082___redArg(lean_object* v_l_571_, lean_object* v_le_572_){
_start:
{
lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_573_ = l_List_lengthTR___redArg(v_l_571_);
v___x_574_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run___redArg(v_le_572_, v___x_573_, v_l_571_);
lean_dec(v___x_573_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_mergeSortTR_u2082(lean_object* v_00_u03b1_575_, lean_object* v_l_576_, lean_object* v_le_577_){
_start:
{
lean_object* v___x_578_; 
v___x_578_ = l_List_MergeSort_Internal_mergeSortTR_u2082___redArg(v_l_576_, v_le_577_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_mergeSort_match__1_splitter___redArg(lean_object* v_x_579_, lean_object* v_x_580_, lean_object* v_h__1_581_, lean_object* v_h__2_582_, lean_object* v_h__3_583_){
_start:
{
if (lean_obj_tag(v_x_579_) == 0)
{
lean_object* v___x_584_; 
lean_dec(v_h__3_583_);
lean_dec(v_h__2_582_);
v___x_584_ = lean_apply_1(v_h__1_581_, v_x_580_);
return v___x_584_;
}
else
{
lean_object* v_tail_585_; 
lean_dec(v_h__1_581_);
v_tail_585_ = lean_ctor_get(v_x_579_, 1);
if (lean_obj_tag(v_tail_585_) == 0)
{
lean_object* v_head_586_; lean_object* v___x_587_; 
lean_dec(v_h__3_583_);
v_head_586_ = lean_ctor_get(v_x_579_, 0);
lean_inc(v_head_586_);
lean_dec_ref_known(v_x_579_, 2);
v___x_587_ = lean_apply_2(v_h__2_582_, v_head_586_, v_x_580_);
return v___x_587_;
}
else
{
lean_object* v_head_588_; lean_object* v_head_589_; lean_object* v_tail_590_; lean_object* v___x_591_; 
lean_inc_ref(v_tail_585_);
lean_dec(v_h__2_582_);
v_head_588_ = lean_ctor_get(v_x_579_, 0);
lean_inc(v_head_588_);
lean_dec_ref_known(v_x_579_, 2);
v_head_589_ = lean_ctor_get(v_tail_585_, 0);
lean_inc(v_head_589_);
v_tail_590_ = lean_ctor_get(v_tail_585_, 1);
lean_inc(v_tail_590_);
lean_dec_ref_known(v_tail_585_, 2);
v___x_591_ = lean_apply_4(v_h__3_583_, v_head_588_, v_head_589_, v_tail_590_, v_x_580_);
return v___x_591_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_mergeSort_match__1_splitter(lean_object* v_00_u03b1_592_, lean_object* v_motive_593_, lean_object* v_x_594_, lean_object* v_x_595_, lean_object* v_h__1_596_, lean_object* v_h__2_597_, lean_object* v_h__3_598_){
_start:
{
if (lean_obj_tag(v_x_594_) == 0)
{
lean_object* v___x_599_; 
lean_dec(v_h__3_598_);
lean_dec(v_h__2_597_);
v___x_599_ = lean_apply_1(v_h__1_596_, v_x_595_);
return v___x_599_;
}
else
{
lean_object* v_tail_600_; 
lean_dec(v_h__1_596_);
v_tail_600_ = lean_ctor_get(v_x_594_, 1);
if (lean_obj_tag(v_tail_600_) == 0)
{
lean_object* v_head_601_; lean_object* v___x_602_; 
lean_dec(v_h__3_598_);
v_head_601_ = lean_ctor_get(v_x_594_, 0);
lean_inc(v_head_601_);
lean_dec_ref_known(v_x_594_, 2);
v___x_602_ = lean_apply_2(v_h__2_597_, v_head_601_, v_x_595_);
return v___x_602_;
}
else
{
lean_object* v_head_603_; lean_object* v_head_604_; lean_object* v_tail_605_; lean_object* v___x_606_; 
lean_inc_ref(v_tail_600_);
lean_dec(v_h__2_597_);
v_head_603_ = lean_ctor_get(v_x_594_, 0);
lean_inc(v_head_603_);
lean_dec_ref_known(v_x_594_, 2);
v_head_604_ = lean_ctor_get(v_tail_600_, 0);
lean_inc(v_head_604_);
v_tail_605_ = lean_ctor_get(v_tail_600_, 1);
lean_inc(v_tail_605_);
lean_dec_ref_known(v_tail_600_, 2);
v___x_606_ = lean_apply_4(v_h__3_598_, v_head_603_, v_head_604_, v_tail_605_, v_x_595_);
return v___x_606_;
}
}
}
}
lean_object* runtime_initialize_Init_Data_List_Sort_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Sort_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Sort_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Internal_Linear(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_List_Sort_Impl(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_List_Sort_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Sort_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Sort_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Internal_Linear(builtin);
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
lean_object* initialize_Init_Data_Nat_Internal_Linear(uint8_t builtin);
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
res = initialize_Init_Data_Nat_Internal_Linear(builtin);
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

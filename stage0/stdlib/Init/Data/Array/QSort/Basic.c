// Lean compiler output
// Module: Init.Data.Array.QSort.Basic
// Imports: public import Init.Data.Vector.Basic public import Init.Data.Ord.Basic import Init.Omega
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
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
static const lean_string_object l_Array_qpartition___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Array_qpartition___auto__1___closed__0 = (const lean_object*)&l_Array_qpartition___auto__1___closed__0_value;
static const lean_string_object l_Array_qpartition___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Array_qpartition___auto__1___closed__1 = (const lean_object*)&l_Array_qpartition___auto__1___closed__1_value;
static const lean_string_object l_Array_qpartition___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Array_qpartition___auto__1___closed__2 = (const lean_object*)&l_Array_qpartition___auto__1___closed__2_value;
static const lean_string_object l_Array_qpartition___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Array_qpartition___auto__1___closed__3 = (const lean_object*)&l_Array_qpartition___auto__1___closed__3_value;
static const lean_ctor_object l_Array_qpartition___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_qpartition___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Array_qpartition___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_qpartition___auto__1___closed__4_value_aux_0),((lean_object*)&l_Array_qpartition___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Array_qpartition___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_qpartition___auto__1___closed__4_value_aux_1),((lean_object*)&l_Array_qpartition___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Array_qpartition___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_qpartition___auto__1___closed__4_value_aux_2),((lean_object*)&l_Array_qpartition___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Array_qpartition___auto__1___closed__4 = (const lean_object*)&l_Array_qpartition___auto__1___closed__4_value;
static const lean_array_object l_Array_qpartition___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_qpartition___auto__1___closed__5 = (const lean_object*)&l_Array_qpartition___auto__1___closed__5_value;
static const lean_string_object l_Array_qpartition___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Array_qpartition___auto__1___closed__6 = (const lean_object*)&l_Array_qpartition___auto__1___closed__6_value;
static const lean_ctor_object l_Array_qpartition___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_qpartition___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Array_qpartition___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_qpartition___auto__1___closed__7_value_aux_0),((lean_object*)&l_Array_qpartition___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Array_qpartition___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_qpartition___auto__1___closed__7_value_aux_1),((lean_object*)&l_Array_qpartition___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Array_qpartition___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_qpartition___auto__1___closed__7_value_aux_2),((lean_object*)&l_Array_qpartition___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Array_qpartition___auto__1___closed__7 = (const lean_object*)&l_Array_qpartition___auto__1___closed__7_value;
static const lean_string_object l_Array_qpartition___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Array_qpartition___auto__1___closed__8 = (const lean_object*)&l_Array_qpartition___auto__1___closed__8_value;
static const lean_ctor_object l_Array_qpartition___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_qpartition___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Array_qpartition___auto__1___closed__9 = (const lean_object*)&l_Array_qpartition___auto__1___closed__9_value;
static const lean_string_object l_Array_qpartition___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "omega"};
static const lean_object* l_Array_qpartition___auto__1___closed__10 = (const lean_object*)&l_Array_qpartition___auto__1___closed__10_value;
static const lean_ctor_object l_Array_qpartition___auto__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_qpartition___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Array_qpartition___auto__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_qpartition___auto__1___closed__11_value_aux_0),((lean_object*)&l_Array_qpartition___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Array_qpartition___auto__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_qpartition___auto__1___closed__11_value_aux_1),((lean_object*)&l_Array_qpartition___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Array_qpartition___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_qpartition___auto__1___closed__11_value_aux_2),((lean_object*)&l_Array_qpartition___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(138, 49, 229, 237, 137, 52, 176, 206)}};
static const lean_object* l_Array_qpartition___auto__1___closed__11 = (const lean_object*)&l_Array_qpartition___auto__1___closed__11_value;
static lean_once_cell_t l_Array_qpartition___auto__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_qpartition___auto__1___closed__12;
static lean_once_cell_t l_Array_qpartition___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_qpartition___auto__1___closed__13;
static const lean_string_object l_Array_qpartition___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Array_qpartition___auto__1___closed__14 = (const lean_object*)&l_Array_qpartition___auto__1___closed__14_value;
static const lean_ctor_object l_Array_qpartition___auto__1___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_qpartition___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Array_qpartition___auto__1___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_qpartition___auto__1___closed__15_value_aux_0),((lean_object*)&l_Array_qpartition___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Array_qpartition___auto__1___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_qpartition___auto__1___closed__15_value_aux_1),((lean_object*)&l_Array_qpartition___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Array_qpartition___auto__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_qpartition___auto__1___closed__15_value_aux_2),((lean_object*)&l_Array_qpartition___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l_Array_qpartition___auto__1___closed__15 = (const lean_object*)&l_Array_qpartition___auto__1___closed__15_value;
static const lean_ctor_object l_Array_qpartition___auto__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Array_qpartition___auto__1___closed__9_value),((lean_object*)&l_Array_qpartition___auto__1___closed__5_value)}};
static const lean_object* l_Array_qpartition___auto__1___closed__16 = (const lean_object*)&l_Array_qpartition___auto__1___closed__16_value;
static lean_once_cell_t l_Array_qpartition___auto__1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_qpartition___auto__1___closed__17;
static lean_once_cell_t l_Array_qpartition___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_qpartition___auto__1___closed__18;
static lean_once_cell_t l_Array_qpartition___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_qpartition___auto__1___closed__19;
static lean_once_cell_t l_Array_qpartition___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_qpartition___auto__1___closed__20;
static lean_once_cell_t l_Array_qpartition___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_qpartition___auto__1___closed__21;
static lean_once_cell_t l_Array_qpartition___auto__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_qpartition___auto__1___closed__22;
static lean_once_cell_t l_Array_qpartition___auto__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_qpartition___auto__1___closed__23;
static lean_once_cell_t l_Array_qpartition___auto__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_qpartition___auto__1___closed__24;
static lean_once_cell_t l_Array_qpartition___auto__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_qpartition___auto__1___closed__25;
static lean_once_cell_t l_Array_qpartition___auto__1___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_qpartition___auto__1___closed__26;
LEAN_EXPORT lean_object* l_Array_qpartition___auto__1;
LEAN_EXPORT lean_object* l_Array_qpartition___auto__3;
LEAN_EXPORT lean_object* l_Array_qpartition___auto__5;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition___auto__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition___auto__4;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition___auto__6;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qpartition___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qpartition(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qpartition___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_qsort___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l_Array_qsort___auto__1___closed__0 = (const lean_object*)&l_Array_qsort___auto__1___closed__0_value;
static const lean_ctor_object l_Array_qsort___auto__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_qpartition___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Array_qsort___auto__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_qsort___auto__1___closed__1_value_aux_0),((lean_object*)&l_Array_qpartition___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Array_qsort___auto__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_qsort___auto__1___closed__1_value_aux_1),((lean_object*)&l_Array_qpartition___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Array_qsort___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_qsort___auto__1___closed__1_value_aux_2),((lean_object*)&l_Array_qsort___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l_Array_qsort___auto__1___closed__1 = (const lean_object*)&l_Array_qsort___auto__1___closed__1_value;
static lean_once_cell_t l_Array_qsort___auto__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_qsort___auto__1___closed__2;
static lean_once_cell_t l_Array_qsort___auto__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_qsort___auto__1___closed__3;
static const lean_string_object l_Array_qsort___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Array_qsort___auto__1___closed__4 = (const lean_object*)&l_Array_qsort___auto__1___closed__4_value;
static const lean_string_object l_Array_qsort___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l_Array_qsort___auto__1___closed__5 = (const lean_object*)&l_Array_qsort___auto__1___closed__5_value;
static const lean_ctor_object l_Array_qsort___auto__1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_qpartition___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Array_qsort___auto__1___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_qsort___auto__1___closed__6_value_aux_0),((lean_object*)&l_Array_qpartition___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Array_qsort___auto__1___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_qsort___auto__1___closed__6_value_aux_1),((lean_object*)&l_Array_qsort___auto__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Array_qsort___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_qsort___auto__1___closed__6_value_aux_2),((lean_object*)&l_Array_qsort___auto__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l_Array_qsort___auto__1___closed__6 = (const lean_object*)&l_Array_qsort___auto__1___closed__6_value;
static const lean_string_object l_Array_qsort___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l_Array_qsort___auto__1___closed__7 = (const lean_object*)&l_Array_qsort___auto__1___closed__7_value;
static const lean_ctor_object l_Array_qsort___auto__1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_qpartition___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Array_qsort___auto__1___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_qsort___auto__1___closed__8_value_aux_0),((lean_object*)&l_Array_qpartition___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Array_qsort___auto__1___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_qsort___auto__1___closed__8_value_aux_1),((lean_object*)&l_Array_qsort___auto__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Array_qsort___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_qsort___auto__1___closed__8_value_aux_2),((lean_object*)&l_Array_qsort___auto__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l_Array_qsort___auto__1___closed__8 = (const lean_object*)&l_Array_qsort___auto__1___closed__8_value;
static const lean_string_object l_Array_qsort___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Array_qsort___auto__1___closed__9 = (const lean_object*)&l_Array_qsort___auto__1___closed__9_value;
static lean_once_cell_t l_Array_qsort___auto__1___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_qsort___auto__1___closed__10;
static lean_once_cell_t l_Array_qsort___auto__1___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_qsort___auto__1___closed__11;
static const lean_string_object l_Array_qsort___auto__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l_Array_qsort___auto__1___closed__12 = (const lean_object*)&l_Array_qsort___auto__1___closed__12_value;
static const lean_ctor_object l_Array_qsort___auto__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_qsort___auto__1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l_Array_qsort___auto__1___closed__13 = (const lean_object*)&l_Array_qsort___auto__1___closed__13_value;
static const lean_string_object l_Array_qsort___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "[anonymous]"};
static const lean_object* l_Array_qsort___auto__1___closed__14 = (const lean_object*)&l_Array_qsort___auto__1___closed__14_value;
static const lean_ctor_object l_Array_qsort___auto__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Array_qsort___auto__1___closed__14_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(11) << 1) | 1))}};
static const lean_object* l_Array_qsort___auto__1___closed__15 = (const lean_object*)&l_Array_qsort___auto__1___closed__15_value;
static const lean_ctor_object l_Array_qsort___auto__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 3}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Array_qsort___auto__1___closed__15_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Array_qsort___auto__1___closed__16 = (const lean_object*)&l_Array_qsort___auto__1___closed__16_value;
static lean_once_cell_t l_Array_qsort___auto__1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_qsort___auto__1___closed__17;
static lean_once_cell_t l_Array_qsort___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_qsort___auto__1___closed__18;
static lean_once_cell_t l_Array_qsort___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_qsort___auto__1___closed__19;
static lean_once_cell_t l_Array_qsort___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_qsort___auto__1___closed__20;
static lean_once_cell_t l_Array_qsort___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_qsort___auto__1___closed__21;
static const lean_string_object l_Array_qsort___auto__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "term_<_"};
static const lean_object* l_Array_qsort___auto__1___closed__22 = (const lean_object*)&l_Array_qsort___auto__1___closed__22_value;
static const lean_ctor_object l_Array_qsort___auto__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_qsort___auto__1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(192, 242, 106, 74, 199, 131, 133, 95)}};
static const lean_object* l_Array_qsort___auto__1___closed__23 = (const lean_object*)&l_Array_qsort___auto__1___closed__23_value;
static const lean_string_object l_Array_qsort___auto__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cdot"};
static const lean_object* l_Array_qsort___auto__1___closed__24 = (const lean_object*)&l_Array_qsort___auto__1___closed__24_value;
static const lean_ctor_object l_Array_qsort___auto__1___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_qpartition___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Array_qsort___auto__1___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_qsort___auto__1___closed__25_value_aux_0),((lean_object*)&l_Array_qpartition___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Array_qsort___auto__1___closed__25_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_qsort___auto__1___closed__25_value_aux_1),((lean_object*)&l_Array_qsort___auto__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Array_qsort___auto__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_qsort___auto__1___closed__25_value_aux_2),((lean_object*)&l_Array_qsort___auto__1___closed__24_value),LEAN_SCALAR_PTR_LITERAL(215, 94, 65, 66, 49, 100, 151, 85)}};
static const lean_object* l_Array_qsort___auto__1___closed__25 = (const lean_object*)&l_Array_qsort___auto__1___closed__25_value;
static const lean_string_object l_Array_qsort___auto__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 1, .m_data = "·"};
static const lean_object* l_Array_qsort___auto__1___closed__26 = (const lean_object*)&l_Array_qsort___auto__1___closed__26_value;
static lean_once_cell_t l_Array_qsort___auto__1___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_qsort___auto__1___closed__27;
static lean_once_cell_t l_Array_qsort___auto__1___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_qsort___auto__1___closed__28;
static lean_once_cell_t l_Array_qsort___auto__1___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_qsort___auto__1___closed__29;
static lean_once_cell_t l_Array_qsort___auto__1___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_qsort___auto__1___closed__30;
static lean_once_cell_t l_Array_qsort___auto__1___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_qsort___auto__1___closed__31;
static const lean_string_object l_Array_qsort___auto__1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "<"};
static const lean_object* l_Array_qsort___auto__1___closed__32 = (const lean_object*)&l_Array_qsort___auto__1___closed__32_value;
static lean_once_cell_t l_Array_qsort___auto__1___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_qsort___auto__1___closed__33;
static lean_once_cell_t l_Array_qsort___auto__1___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_qsort___auto__1___closed__34;
static lean_once_cell_t l_Array_qsort___auto__1___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_qsort___auto__1___closed__35;
static lean_once_cell_t l_Array_qsort___auto__1___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_qsort___auto__1___closed__36;
static lean_once_cell_t l_Array_qsort___auto__1___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_qsort___auto__1___closed__37;
static const lean_string_object l_Array_qsort___auto__1___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Array_qsort___auto__1___closed__38 = (const lean_object*)&l_Array_qsort___auto__1___closed__38_value;
static lean_once_cell_t l_Array_qsort___auto__1___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_qsort___auto__1___closed__39;
static lean_once_cell_t l_Array_qsort___auto__1___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_qsort___auto__1___closed__40;
static lean_once_cell_t l_Array_qsort___auto__1___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_qsort___auto__1___closed__41;
static lean_once_cell_t l_Array_qsort___auto__1___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_qsort___auto__1___closed__42;
static lean_once_cell_t l_Array_qsort___auto__1___closed__43_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_qsort___auto__1___closed__43;
static lean_once_cell_t l_Array_qsort___auto__1___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_qsort___auto__1___closed__44;
static lean_once_cell_t l_Array_qsort___auto__1___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_qsort___auto__1___closed__45;
static lean_once_cell_t l_Array_qsort___auto__1___closed__46_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_qsort___auto__1___closed__46;
static lean_once_cell_t l_Array_qsort___auto__1___closed__47_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_qsort___auto__1___closed__47;
static lean_once_cell_t l_Array_qsort___auto__1___closed__48_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_qsort___auto__1___closed__48;
static lean_once_cell_t l_Array_qsort___auto__1___closed__49_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_qsort___auto__1___closed__49;
LEAN_EXPORT lean_object* l_Array_qsort___auto__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort___auto__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort___auto__4;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort___auto__6;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_match__8_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_match__8_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_match__8_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_qsortOrd___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsortOrd___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsortOrd___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsortOrd(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Array_qpartition___auto__1___closed__12(void){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_27_ = ((lean_object*)(l_Array_qpartition___auto__1___closed__10));
v___x_28_ = l_Lean_mkAtom(v___x_27_);
return v___x_28_;
}
}
static lean_object* _init_l_Array_qpartition___auto__1___closed__13(void){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_29_ = lean_obj_once(&l_Array_qpartition___auto__1___closed__12, &l_Array_qpartition___auto__1___closed__12_once, _init_l_Array_qpartition___auto__1___closed__12);
v___x_30_ = ((lean_object*)(l_Array_qpartition___auto__1___closed__5));
v___x_31_ = lean_array_push(v___x_30_, v___x_29_);
return v___x_31_;
}
}
static lean_object* _init_l_Array_qpartition___auto__1___closed__17(void){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_42_ = ((lean_object*)(l_Array_qpartition___auto__1___closed__16));
v___x_43_ = ((lean_object*)(l_Array_qpartition___auto__1___closed__5));
v___x_44_ = lean_array_push(v___x_43_, v___x_42_);
return v___x_44_;
}
}
static lean_object* _init_l_Array_qpartition___auto__1___closed__18(void){
_start:
{
lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_45_ = lean_obj_once(&l_Array_qpartition___auto__1___closed__17, &l_Array_qpartition___auto__1___closed__17_once, _init_l_Array_qpartition___auto__1___closed__17);
v___x_46_ = ((lean_object*)(l_Array_qpartition___auto__1___closed__15));
v___x_47_ = lean_box(2);
v___x_48_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_48_, 0, v___x_47_);
lean_ctor_set(v___x_48_, 1, v___x_46_);
lean_ctor_set(v___x_48_, 2, v___x_45_);
return v___x_48_;
}
}
static lean_object* _init_l_Array_qpartition___auto__1___closed__19(void){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_49_ = lean_obj_once(&l_Array_qpartition___auto__1___closed__18, &l_Array_qpartition___auto__1___closed__18_once, _init_l_Array_qpartition___auto__1___closed__18);
v___x_50_ = lean_obj_once(&l_Array_qpartition___auto__1___closed__13, &l_Array_qpartition___auto__1___closed__13_once, _init_l_Array_qpartition___auto__1___closed__13);
v___x_51_ = lean_array_push(v___x_50_, v___x_49_);
return v___x_51_;
}
}
static lean_object* _init_l_Array_qpartition___auto__1___closed__20(void){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_52_ = lean_obj_once(&l_Array_qpartition___auto__1___closed__19, &l_Array_qpartition___auto__1___closed__19_once, _init_l_Array_qpartition___auto__1___closed__19);
v___x_53_ = ((lean_object*)(l_Array_qpartition___auto__1___closed__11));
v___x_54_ = lean_box(2);
v___x_55_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_55_, 0, v___x_54_);
lean_ctor_set(v___x_55_, 1, v___x_53_);
lean_ctor_set(v___x_55_, 2, v___x_52_);
return v___x_55_;
}
}
static lean_object* _init_l_Array_qpartition___auto__1___closed__21(void){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_56_ = lean_obj_once(&l_Array_qpartition___auto__1___closed__20, &l_Array_qpartition___auto__1___closed__20_once, _init_l_Array_qpartition___auto__1___closed__20);
v___x_57_ = ((lean_object*)(l_Array_qpartition___auto__1___closed__5));
v___x_58_ = lean_array_push(v___x_57_, v___x_56_);
return v___x_58_;
}
}
static lean_object* _init_l_Array_qpartition___auto__1___closed__22(void){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_59_ = lean_obj_once(&l_Array_qpartition___auto__1___closed__21, &l_Array_qpartition___auto__1___closed__21_once, _init_l_Array_qpartition___auto__1___closed__21);
v___x_60_ = ((lean_object*)(l_Array_qpartition___auto__1___closed__9));
v___x_61_ = lean_box(2);
v___x_62_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_62_, 0, v___x_61_);
lean_ctor_set(v___x_62_, 1, v___x_60_);
lean_ctor_set(v___x_62_, 2, v___x_59_);
return v___x_62_;
}
}
static lean_object* _init_l_Array_qpartition___auto__1___closed__23(void){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_63_ = lean_obj_once(&l_Array_qpartition___auto__1___closed__22, &l_Array_qpartition___auto__1___closed__22_once, _init_l_Array_qpartition___auto__1___closed__22);
v___x_64_ = ((lean_object*)(l_Array_qpartition___auto__1___closed__5));
v___x_65_ = lean_array_push(v___x_64_, v___x_63_);
return v___x_65_;
}
}
static lean_object* _init_l_Array_qpartition___auto__1___closed__24(void){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_66_ = lean_obj_once(&l_Array_qpartition___auto__1___closed__23, &l_Array_qpartition___auto__1___closed__23_once, _init_l_Array_qpartition___auto__1___closed__23);
v___x_67_ = ((lean_object*)(l_Array_qpartition___auto__1___closed__7));
v___x_68_ = lean_box(2);
v___x_69_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_69_, 0, v___x_68_);
lean_ctor_set(v___x_69_, 1, v___x_67_);
lean_ctor_set(v___x_69_, 2, v___x_66_);
return v___x_69_;
}
}
static lean_object* _init_l_Array_qpartition___auto__1___closed__25(void){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_70_ = lean_obj_once(&l_Array_qpartition___auto__1___closed__24, &l_Array_qpartition___auto__1___closed__24_once, _init_l_Array_qpartition___auto__1___closed__24);
v___x_71_ = ((lean_object*)(l_Array_qpartition___auto__1___closed__5));
v___x_72_ = lean_array_push(v___x_71_, v___x_70_);
return v___x_72_;
}
}
static lean_object* _init_l_Array_qpartition___auto__1___closed__26(void){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_73_ = lean_obj_once(&l_Array_qpartition___auto__1___closed__25, &l_Array_qpartition___auto__1___closed__25_once, _init_l_Array_qpartition___auto__1___closed__25);
v___x_74_ = ((lean_object*)(l_Array_qpartition___auto__1___closed__4));
v___x_75_ = lean_box(2);
v___x_76_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_76_, 0, v___x_75_);
lean_ctor_set(v___x_76_, 1, v___x_74_);
lean_ctor_set(v___x_76_, 2, v___x_73_);
return v___x_76_;
}
}
static lean_object* _init_l_Array_qpartition___auto__1(void){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = lean_obj_once(&l_Array_qpartition___auto__1___closed__26, &l_Array_qpartition___auto__1___closed__26_once, _init_l_Array_qpartition___auto__1___closed__26);
return v___x_77_;
}
}
static lean_object* _init_l_Array_qpartition___auto__3(void){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = lean_obj_once(&l_Array_qpartition___auto__1___closed__26, &l_Array_qpartition___auto__1___closed__26_once, _init_l_Array_qpartition___auto__1___closed__26);
return v___x_78_;
}
}
static lean_object* _init_l_Array_qpartition___auto__5(void){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = lean_obj_once(&l_Array_qpartition___auto__1___closed__26, &l_Array_qpartition___auto__1___closed__26_once, _init_l_Array_qpartition___auto__1___closed__26);
return v___x_79_;
}
}
static lean_object* _init_l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition___auto__2(void){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = lean_obj_once(&l_Array_qpartition___auto__1___closed__26, &l_Array_qpartition___auto__1___closed__26_once, _init_l_Array_qpartition___auto__1___closed__26);
return v___x_80_;
}
}
static lean_object* _init_l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition___auto__4(void){
_start:
{
lean_object* v___x_81_; 
v___x_81_ = lean_obj_once(&l_Array_qpartition___auto__1___closed__26, &l_Array_qpartition___auto__1___closed__26_once, _init_l_Array_qpartition___auto__1___closed__26);
return v___x_81_;
}
}
static lean_object* _init_l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition___auto__6(void){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = lean_obj_once(&l_Array_qpartition___auto__1___closed__26, &l_Array_qpartition___auto__1___closed__26_once, _init_l_Array_qpartition___auto__1___closed__26);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___redArg(lean_object* v_lt_83_, lean_object* v_hi_84_, lean_object* v_pivot_85_, lean_object* v_as_86_, lean_object* v_i_87_, lean_object* v_k_88_){
_start:
{
uint8_t v___x_89_; 
v___x_89_ = lean_nat_dec_lt(v_k_88_, v_hi_84_);
if (v___x_89_ == 0)
{
lean_object* v___x_90_; lean_object* v___x_91_; 
lean_dec(v_k_88_);
lean_dec(v_pivot_85_);
lean_dec_ref(v_lt_83_);
v___x_90_ = lean_array_fswap(v_as_86_, v_i_87_, v_hi_84_);
v___x_91_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_91_, 0, v_i_87_);
lean_ctor_set(v___x_91_, 1, v___x_90_);
return v___x_91_;
}
else
{
lean_object* v___x_92_; lean_object* v___x_93_; uint8_t v___x_94_; 
v___x_92_ = lean_array_fget_borrowed(v_as_86_, v_k_88_);
lean_inc_ref(v_lt_83_);
lean_inc(v_pivot_85_);
lean_inc(v___x_92_);
v___x_93_ = lean_apply_2(v_lt_83_, v___x_92_, v_pivot_85_);
v___x_94_ = lean_unbox(v___x_93_);
if (v___x_94_ == 0)
{
lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_95_ = lean_unsigned_to_nat(1u);
v___x_96_ = lean_nat_add(v_k_88_, v___x_95_);
lean_dec(v_k_88_);
v_k_88_ = v___x_96_;
goto _start;
}
else
{
lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_98_ = lean_array_fswap(v_as_86_, v_i_87_, v_k_88_);
v___x_99_ = lean_unsigned_to_nat(1u);
v___x_100_ = lean_nat_add(v_i_87_, v___x_99_);
lean_dec(v_i_87_);
v___x_101_ = lean_nat_add(v_k_88_, v___x_99_);
lean_dec(v_k_88_);
v_as_86_ = v___x_98_;
v_i_87_ = v___x_100_;
v_k_88_ = v___x_101_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___redArg___boxed(lean_object* v_lt_103_, lean_object* v_hi_104_, lean_object* v_pivot_105_, lean_object* v_as_106_, lean_object* v_i_107_, lean_object* v_k_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___redArg(v_lt_103_, v_hi_104_, v_pivot_105_, v_as_106_, v_i_107_, v_k_108_);
lean_dec(v_hi_104_);
return v_res_109_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop(lean_object* v_00_u03b1_110_, lean_object* v_n_111_, lean_object* v_lt_112_, lean_object* v_lo_113_, lean_object* v_hi_114_, lean_object* v_hhi_115_, lean_object* v_pivot_116_, lean_object* v_as_117_, lean_object* v_i_118_, lean_object* v_k_119_, lean_object* v_ilo_120_, lean_object* v_ik_121_, lean_object* v_w_122_){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___redArg(v_lt_112_, v_hi_114_, v_pivot_116_, v_as_117_, v_i_118_, v_k_119_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___boxed(lean_object* v_00_u03b1_124_, lean_object* v_n_125_, lean_object* v_lt_126_, lean_object* v_lo_127_, lean_object* v_hi_128_, lean_object* v_hhi_129_, lean_object* v_pivot_130_, lean_object* v_as_131_, lean_object* v_i_132_, lean_object* v_k_133_, lean_object* v_ilo_134_, lean_object* v_ik_135_, lean_object* v_w_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop(v_00_u03b1_124_, v_n_125_, v_lt_126_, v_lo_127_, v_hi_128_, v_hhi_129_, v_pivot_130_, v_as_131_, v_i_132_, v_k_133_, v_ilo_134_, v_ik_135_, v_w_136_);
lean_dec(v_hi_128_);
lean_dec(v_lo_127_);
lean_dec(v_n_125_);
return v_res_137_;
}
}
LEAN_EXPORT lean_object* l_Array_qpartition___redArg(lean_object* v_as_138_, lean_object* v_lt_139_, lean_object* v_lo_140_, lean_object* v_hi_141_){
_start:
{
lean_object* v___y_143_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v_mid_148_; lean_object* v___y_150_; lean_object* v___y_157_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; uint8_t v___x_166_; 
v___x_146_ = lean_nat_add(v_lo_140_, v_hi_141_);
v___x_147_ = lean_unsigned_to_nat(1u);
v_mid_148_ = lean_nat_shiftr(v___x_146_, v___x_147_);
lean_dec(v___x_146_);
v___x_163_ = lean_array_fget_borrowed(v_as_138_, v_mid_148_);
v___x_164_ = lean_array_fget_borrowed(v_as_138_, v_lo_140_);
lean_inc_ref(v_lt_139_);
lean_inc(v___x_164_);
lean_inc(v___x_163_);
v___x_165_ = lean_apply_2(v_lt_139_, v___x_163_, v___x_164_);
v___x_166_ = lean_unbox(v___x_165_);
if (v___x_166_ == 0)
{
v___y_157_ = v_as_138_;
goto v___jp_156_;
}
else
{
lean_object* v___x_167_; 
v___x_167_ = lean_array_fswap(v_as_138_, v_lo_140_, v_mid_148_);
v___y_157_ = v___x_167_;
goto v___jp_156_;
}
v___jp_142_:
{
lean_object* v_pivot_144_; lean_object* v___x_145_; 
v_pivot_144_ = lean_array_fget(v___y_143_, v_hi_141_);
lean_inc(v_lo_140_);
v___x_145_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___redArg(v_lt_139_, v_hi_141_, v_pivot_144_, v___y_143_, v_lo_140_, v_lo_140_);
return v___x_145_;
}
v___jp_149_:
{
lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; uint8_t v___x_154_; 
v___x_151_ = lean_array_fget_borrowed(v___y_150_, v_mid_148_);
v___x_152_ = lean_array_fget_borrowed(v___y_150_, v_hi_141_);
lean_inc_ref(v_lt_139_);
lean_inc(v___x_152_);
lean_inc(v___x_151_);
v___x_153_ = lean_apply_2(v_lt_139_, v___x_151_, v___x_152_);
v___x_154_ = lean_unbox(v___x_153_);
if (v___x_154_ == 0)
{
lean_dec(v_mid_148_);
v___y_143_ = v___y_150_;
goto v___jp_142_;
}
else
{
lean_object* v___x_155_; 
v___x_155_ = lean_array_fswap(v___y_150_, v_mid_148_, v_hi_141_);
lean_dec(v_mid_148_);
v___y_143_ = v___x_155_;
goto v___jp_142_;
}
}
v___jp_156_:
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; uint8_t v___x_161_; 
v___x_158_ = lean_array_fget_borrowed(v___y_157_, v_hi_141_);
v___x_159_ = lean_array_fget_borrowed(v___y_157_, v_lo_140_);
lean_inc_ref(v_lt_139_);
lean_inc(v___x_159_);
lean_inc(v___x_158_);
v___x_160_ = lean_apply_2(v_lt_139_, v___x_158_, v___x_159_);
v___x_161_ = lean_unbox(v___x_160_);
if (v___x_161_ == 0)
{
v___y_150_ = v___y_157_;
goto v___jp_149_;
}
else
{
lean_object* v___x_162_; 
v___x_162_ = lean_array_fswap(v___y_157_, v_lo_140_, v_hi_141_);
v___y_150_ = v___x_162_;
goto v___jp_149_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_qpartition___redArg___boxed(lean_object* v_as_168_, lean_object* v_lt_169_, lean_object* v_lo_170_, lean_object* v_hi_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l_Array_qpartition___redArg(v_as_168_, v_lt_169_, v_lo_170_, v_hi_171_);
lean_dec(v_hi_171_);
return v_res_172_;
}
}
LEAN_EXPORT lean_object* l_Array_qpartition(lean_object* v_00_u03b1_173_, lean_object* v_n_174_, lean_object* v_as_175_, lean_object* v_lt_176_, lean_object* v_lo_177_, lean_object* v_hi_178_, lean_object* v_w_179_, lean_object* v_hlo_180_, lean_object* v_hhi_181_){
_start:
{
lean_object* v___y_183_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v_mid_188_; lean_object* v___y_190_; lean_object* v___y_197_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; uint8_t v___x_206_; 
v___x_186_ = lean_nat_add(v_lo_177_, v_hi_178_);
v___x_187_ = lean_unsigned_to_nat(1u);
v_mid_188_ = lean_nat_shiftr(v___x_186_, v___x_187_);
lean_dec(v___x_186_);
v___x_203_ = lean_array_fget_borrowed(v_as_175_, v_mid_188_);
v___x_204_ = lean_array_fget_borrowed(v_as_175_, v_lo_177_);
lean_inc_ref(v_lt_176_);
lean_inc(v___x_204_);
lean_inc(v___x_203_);
v___x_205_ = lean_apply_2(v_lt_176_, v___x_203_, v___x_204_);
v___x_206_ = lean_unbox(v___x_205_);
if (v___x_206_ == 0)
{
v___y_197_ = v_as_175_;
goto v___jp_196_;
}
else
{
lean_object* v___x_207_; 
v___x_207_ = lean_array_fswap(v_as_175_, v_lo_177_, v_mid_188_);
v___y_197_ = v___x_207_;
goto v___jp_196_;
}
v___jp_182_:
{
lean_object* v_pivot_184_; lean_object* v___x_185_; 
v_pivot_184_ = lean_array_fget(v___y_183_, v_hi_178_);
lean_inc(v_lo_177_);
v___x_185_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___redArg(v_lt_176_, v_hi_178_, v_pivot_184_, v___y_183_, v_lo_177_, v_lo_177_);
return v___x_185_;
}
v___jp_189_:
{
lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; uint8_t v___x_194_; 
v___x_191_ = lean_array_fget_borrowed(v___y_190_, v_mid_188_);
v___x_192_ = lean_array_fget_borrowed(v___y_190_, v_hi_178_);
lean_inc_ref(v_lt_176_);
lean_inc(v___x_192_);
lean_inc(v___x_191_);
v___x_193_ = lean_apply_2(v_lt_176_, v___x_191_, v___x_192_);
v___x_194_ = lean_unbox(v___x_193_);
if (v___x_194_ == 0)
{
lean_dec(v_mid_188_);
v___y_183_ = v___y_190_;
goto v___jp_182_;
}
else
{
lean_object* v___x_195_; 
v___x_195_ = lean_array_fswap(v___y_190_, v_mid_188_, v_hi_178_);
lean_dec(v_mid_188_);
v___y_183_ = v___x_195_;
goto v___jp_182_;
}
}
v___jp_196_:
{
lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; uint8_t v___x_201_; 
v___x_198_ = lean_array_fget_borrowed(v___y_197_, v_hi_178_);
v___x_199_ = lean_array_fget_borrowed(v___y_197_, v_lo_177_);
lean_inc_ref(v_lt_176_);
lean_inc(v___x_199_);
lean_inc(v___x_198_);
v___x_200_ = lean_apply_2(v_lt_176_, v___x_198_, v___x_199_);
v___x_201_ = lean_unbox(v___x_200_);
if (v___x_201_ == 0)
{
v___y_190_ = v___y_197_;
goto v___jp_189_;
}
else
{
lean_object* v___x_202_; 
v___x_202_ = lean_array_fswap(v___y_197_, v_lo_177_, v_hi_178_);
v___y_190_ = v___x_202_;
goto v___jp_189_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_qpartition___boxed(lean_object* v_00_u03b1_208_, lean_object* v_n_209_, lean_object* v_as_210_, lean_object* v_lt_211_, lean_object* v_lo_212_, lean_object* v_hi_213_, lean_object* v_w_214_, lean_object* v_hlo_215_, lean_object* v_hhi_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l_Array_qpartition(v_00_u03b1_208_, v_n_209_, v_as_210_, v_lt_211_, v_lo_212_, v_hi_213_, v_w_214_, v_hlo_215_, v_hhi_216_);
lean_dec(v_hi_213_);
lean_dec(v_n_209_);
return v_res_217_;
}
}
static lean_object* _init_l_Array_qsort___auto__1___closed__2(void){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_224_ = ((lean_object*)(l_Array_qsort___auto__1___closed__0));
v___x_225_ = l_Lean_mkAtom(v___x_224_);
return v___x_225_;
}
}
static lean_object* _init_l_Array_qsort___auto__1___closed__3(void){
_start:
{
lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_226_ = lean_obj_once(&l_Array_qsort___auto__1___closed__2, &l_Array_qsort___auto__1___closed__2_once, _init_l_Array_qsort___auto__1___closed__2);
v___x_227_ = ((lean_object*)(l_Array_qpartition___auto__1___closed__5));
v___x_228_ = lean_array_push(v___x_227_, v___x_226_);
return v___x_228_;
}
}
static lean_object* _init_l_Array_qsort___auto__1___closed__10(void){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_243_ = ((lean_object*)(l_Array_qsort___auto__1___closed__9));
v___x_244_ = l_Lean_mkAtom(v___x_243_);
return v___x_244_;
}
}
static lean_object* _init_l_Array_qsort___auto__1___closed__11(void){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_245_ = lean_obj_once(&l_Array_qsort___auto__1___closed__10, &l_Array_qsort___auto__1___closed__10_once, _init_l_Array_qsort___auto__1___closed__10);
v___x_246_ = ((lean_object*)(l_Array_qpartition___auto__1___closed__5));
v___x_247_ = lean_array_push(v___x_246_, v___x_245_);
return v___x_247_;
}
}
static lean_object* _init_l_Array_qsort___auto__1___closed__17(void){
_start:
{
lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_261_ = ((lean_object*)(l_Array_qsort___auto__1___closed__16));
v___x_262_ = ((lean_object*)(l_Array_qpartition___auto__1___closed__5));
v___x_263_ = lean_array_push(v___x_262_, v___x_261_);
return v___x_263_;
}
}
static lean_object* _init_l_Array_qsort___auto__1___closed__18(void){
_start:
{
lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_264_ = lean_obj_once(&l_Array_qsort___auto__1___closed__17, &l_Array_qsort___auto__1___closed__17_once, _init_l_Array_qsort___auto__1___closed__17);
v___x_265_ = ((lean_object*)(l_Array_qsort___auto__1___closed__13));
v___x_266_ = lean_box(2);
v___x_267_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_267_, 0, v___x_266_);
lean_ctor_set(v___x_267_, 1, v___x_265_);
lean_ctor_set(v___x_267_, 2, v___x_264_);
return v___x_267_;
}
}
static lean_object* _init_l_Array_qsort___auto__1___closed__19(void){
_start:
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_268_ = lean_obj_once(&l_Array_qsort___auto__1___closed__18, &l_Array_qsort___auto__1___closed__18_once, _init_l_Array_qsort___auto__1___closed__18);
v___x_269_ = lean_obj_once(&l_Array_qsort___auto__1___closed__11, &l_Array_qsort___auto__1___closed__11_once, _init_l_Array_qsort___auto__1___closed__11);
v___x_270_ = lean_array_push(v___x_269_, v___x_268_);
return v___x_270_;
}
}
static lean_object* _init_l_Array_qsort___auto__1___closed__20(void){
_start:
{
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_271_ = lean_obj_once(&l_Array_qsort___auto__1___closed__19, &l_Array_qsort___auto__1___closed__19_once, _init_l_Array_qsort___auto__1___closed__19);
v___x_272_ = ((lean_object*)(l_Array_qsort___auto__1___closed__8));
v___x_273_ = lean_box(2);
v___x_274_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_274_, 0, v___x_273_);
lean_ctor_set(v___x_274_, 1, v___x_272_);
lean_ctor_set(v___x_274_, 2, v___x_271_);
return v___x_274_;
}
}
static lean_object* _init_l_Array_qsort___auto__1___closed__21(void){
_start:
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_275_ = lean_obj_once(&l_Array_qsort___auto__1___closed__20, &l_Array_qsort___auto__1___closed__20_once, _init_l_Array_qsort___auto__1___closed__20);
v___x_276_ = ((lean_object*)(l_Array_qpartition___auto__1___closed__5));
v___x_277_ = lean_array_push(v___x_276_, v___x_275_);
return v___x_277_;
}
}
static lean_object* _init_l_Array_qsort___auto__1___closed__27(void){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_288_ = ((lean_object*)(l_Array_qsort___auto__1___closed__26));
v___x_289_ = l_Lean_mkAtom(v___x_288_);
return v___x_289_;
}
}
static lean_object* _init_l_Array_qsort___auto__1___closed__28(void){
_start:
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_290_ = lean_obj_once(&l_Array_qsort___auto__1___closed__27, &l_Array_qsort___auto__1___closed__27_once, _init_l_Array_qsort___auto__1___closed__27);
v___x_291_ = ((lean_object*)(l_Array_qpartition___auto__1___closed__5));
v___x_292_ = lean_array_push(v___x_291_, v___x_290_);
return v___x_292_;
}
}
static lean_object* _init_l_Array_qsort___auto__1___closed__29(void){
_start:
{
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_293_ = lean_obj_once(&l_Array_qsort___auto__1___closed__18, &l_Array_qsort___auto__1___closed__18_once, _init_l_Array_qsort___auto__1___closed__18);
v___x_294_ = lean_obj_once(&l_Array_qsort___auto__1___closed__28, &l_Array_qsort___auto__1___closed__28_once, _init_l_Array_qsort___auto__1___closed__28);
v___x_295_ = lean_array_push(v___x_294_, v___x_293_);
return v___x_295_;
}
}
static lean_object* _init_l_Array_qsort___auto__1___closed__30(void){
_start:
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_296_ = lean_obj_once(&l_Array_qsort___auto__1___closed__29, &l_Array_qsort___auto__1___closed__29_once, _init_l_Array_qsort___auto__1___closed__29);
v___x_297_ = ((lean_object*)(l_Array_qsort___auto__1___closed__25));
v___x_298_ = lean_box(2);
v___x_299_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_299_, 0, v___x_298_);
lean_ctor_set(v___x_299_, 1, v___x_297_);
lean_ctor_set(v___x_299_, 2, v___x_296_);
return v___x_299_;
}
}
static lean_object* _init_l_Array_qsort___auto__1___closed__31(void){
_start:
{
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_300_ = lean_obj_once(&l_Array_qsort___auto__1___closed__30, &l_Array_qsort___auto__1___closed__30_once, _init_l_Array_qsort___auto__1___closed__30);
v___x_301_ = ((lean_object*)(l_Array_qpartition___auto__1___closed__5));
v___x_302_ = lean_array_push(v___x_301_, v___x_300_);
return v___x_302_;
}
}
static lean_object* _init_l_Array_qsort___auto__1___closed__33(void){
_start:
{
lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_304_ = ((lean_object*)(l_Array_qsort___auto__1___closed__32));
v___x_305_ = l_Lean_mkAtom(v___x_304_);
return v___x_305_;
}
}
static lean_object* _init_l_Array_qsort___auto__1___closed__34(void){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_306_ = lean_obj_once(&l_Array_qsort___auto__1___closed__33, &l_Array_qsort___auto__1___closed__33_once, _init_l_Array_qsort___auto__1___closed__33);
v___x_307_ = lean_obj_once(&l_Array_qsort___auto__1___closed__31, &l_Array_qsort___auto__1___closed__31_once, _init_l_Array_qsort___auto__1___closed__31);
v___x_308_ = lean_array_push(v___x_307_, v___x_306_);
return v___x_308_;
}
}
static lean_object* _init_l_Array_qsort___auto__1___closed__35(void){
_start:
{
lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_309_ = lean_obj_once(&l_Array_qsort___auto__1___closed__30, &l_Array_qsort___auto__1___closed__30_once, _init_l_Array_qsort___auto__1___closed__30);
v___x_310_ = lean_obj_once(&l_Array_qsort___auto__1___closed__34, &l_Array_qsort___auto__1___closed__34_once, _init_l_Array_qsort___auto__1___closed__34);
v___x_311_ = lean_array_push(v___x_310_, v___x_309_);
return v___x_311_;
}
}
static lean_object* _init_l_Array_qsort___auto__1___closed__36(void){
_start:
{
lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_312_ = lean_obj_once(&l_Array_qsort___auto__1___closed__35, &l_Array_qsort___auto__1___closed__35_once, _init_l_Array_qsort___auto__1___closed__35);
v___x_313_ = ((lean_object*)(l_Array_qsort___auto__1___closed__23));
v___x_314_ = lean_box(2);
v___x_315_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_315_, 0, v___x_314_);
lean_ctor_set(v___x_315_, 1, v___x_313_);
lean_ctor_set(v___x_315_, 2, v___x_312_);
return v___x_315_;
}
}
static lean_object* _init_l_Array_qsort___auto__1___closed__37(void){
_start:
{
lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_316_ = lean_obj_once(&l_Array_qsort___auto__1___closed__36, &l_Array_qsort___auto__1___closed__36_once, _init_l_Array_qsort___auto__1___closed__36);
v___x_317_ = lean_obj_once(&l_Array_qsort___auto__1___closed__21, &l_Array_qsort___auto__1___closed__21_once, _init_l_Array_qsort___auto__1___closed__21);
v___x_318_ = lean_array_push(v___x_317_, v___x_316_);
return v___x_318_;
}
}
static lean_object* _init_l_Array_qsort___auto__1___closed__39(void){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_320_ = ((lean_object*)(l_Array_qsort___auto__1___closed__38));
v___x_321_ = l_Lean_mkAtom(v___x_320_);
return v___x_321_;
}
}
static lean_object* _init_l_Array_qsort___auto__1___closed__40(void){
_start:
{
lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_322_ = lean_obj_once(&l_Array_qsort___auto__1___closed__39, &l_Array_qsort___auto__1___closed__39_once, _init_l_Array_qsort___auto__1___closed__39);
v___x_323_ = lean_obj_once(&l_Array_qsort___auto__1___closed__37, &l_Array_qsort___auto__1___closed__37_once, _init_l_Array_qsort___auto__1___closed__37);
v___x_324_ = lean_array_push(v___x_323_, v___x_322_);
return v___x_324_;
}
}
static lean_object* _init_l_Array_qsort___auto__1___closed__41(void){
_start:
{
lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_325_ = lean_obj_once(&l_Array_qsort___auto__1___closed__40, &l_Array_qsort___auto__1___closed__40_once, _init_l_Array_qsort___auto__1___closed__40);
v___x_326_ = ((lean_object*)(l_Array_qsort___auto__1___closed__6));
v___x_327_ = lean_box(2);
v___x_328_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_328_, 0, v___x_327_);
lean_ctor_set(v___x_328_, 1, v___x_326_);
lean_ctor_set(v___x_328_, 2, v___x_325_);
return v___x_328_;
}
}
static lean_object* _init_l_Array_qsort___auto__1___closed__42(void){
_start:
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_329_ = lean_obj_once(&l_Array_qsort___auto__1___closed__41, &l_Array_qsort___auto__1___closed__41_once, _init_l_Array_qsort___auto__1___closed__41);
v___x_330_ = lean_obj_once(&l_Array_qsort___auto__1___closed__3, &l_Array_qsort___auto__1___closed__3_once, _init_l_Array_qsort___auto__1___closed__3);
v___x_331_ = lean_array_push(v___x_330_, v___x_329_);
return v___x_331_;
}
}
static lean_object* _init_l_Array_qsort___auto__1___closed__43(void){
_start:
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_332_ = lean_obj_once(&l_Array_qsort___auto__1___closed__42, &l_Array_qsort___auto__1___closed__42_once, _init_l_Array_qsort___auto__1___closed__42);
v___x_333_ = ((lean_object*)(l_Array_qsort___auto__1___closed__1));
v___x_334_ = lean_box(2);
v___x_335_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
lean_ctor_set(v___x_335_, 1, v___x_333_);
lean_ctor_set(v___x_335_, 2, v___x_332_);
return v___x_335_;
}
}
static lean_object* _init_l_Array_qsort___auto__1___closed__44(void){
_start:
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_336_ = lean_obj_once(&l_Array_qsort___auto__1___closed__43, &l_Array_qsort___auto__1___closed__43_once, _init_l_Array_qsort___auto__1___closed__43);
v___x_337_ = ((lean_object*)(l_Array_qpartition___auto__1___closed__5));
v___x_338_ = lean_array_push(v___x_337_, v___x_336_);
return v___x_338_;
}
}
static lean_object* _init_l_Array_qsort___auto__1___closed__45(void){
_start:
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_339_ = lean_obj_once(&l_Array_qsort___auto__1___closed__44, &l_Array_qsort___auto__1___closed__44_once, _init_l_Array_qsort___auto__1___closed__44);
v___x_340_ = ((lean_object*)(l_Array_qpartition___auto__1___closed__9));
v___x_341_ = lean_box(2);
v___x_342_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_342_, 0, v___x_341_);
lean_ctor_set(v___x_342_, 1, v___x_340_);
lean_ctor_set(v___x_342_, 2, v___x_339_);
return v___x_342_;
}
}
static lean_object* _init_l_Array_qsort___auto__1___closed__46(void){
_start:
{
lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_343_ = lean_obj_once(&l_Array_qsort___auto__1___closed__45, &l_Array_qsort___auto__1___closed__45_once, _init_l_Array_qsort___auto__1___closed__45);
v___x_344_ = ((lean_object*)(l_Array_qpartition___auto__1___closed__5));
v___x_345_ = lean_array_push(v___x_344_, v___x_343_);
return v___x_345_;
}
}
static lean_object* _init_l_Array_qsort___auto__1___closed__47(void){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_346_ = lean_obj_once(&l_Array_qsort___auto__1___closed__46, &l_Array_qsort___auto__1___closed__46_once, _init_l_Array_qsort___auto__1___closed__46);
v___x_347_ = ((lean_object*)(l_Array_qpartition___auto__1___closed__7));
v___x_348_ = lean_box(2);
v___x_349_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_349_, 0, v___x_348_);
lean_ctor_set(v___x_349_, 1, v___x_347_);
lean_ctor_set(v___x_349_, 2, v___x_346_);
return v___x_349_;
}
}
static lean_object* _init_l_Array_qsort___auto__1___closed__48(void){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_350_ = lean_obj_once(&l_Array_qsort___auto__1___closed__47, &l_Array_qsort___auto__1___closed__47_once, _init_l_Array_qsort___auto__1___closed__47);
v___x_351_ = ((lean_object*)(l_Array_qpartition___auto__1___closed__5));
v___x_352_ = lean_array_push(v___x_351_, v___x_350_);
return v___x_352_;
}
}
static lean_object* _init_l_Array_qsort___auto__1___closed__49(void){
_start:
{
lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_353_ = lean_obj_once(&l_Array_qsort___auto__1___closed__48, &l_Array_qsort___auto__1___closed__48_once, _init_l_Array_qsort___auto__1___closed__48);
v___x_354_ = ((lean_object*)(l_Array_qpartition___auto__1___closed__4));
v___x_355_ = lean_box(2);
v___x_356_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_356_, 0, v___x_355_);
lean_ctor_set(v___x_356_, 1, v___x_354_);
lean_ctor_set(v___x_356_, 2, v___x_353_);
return v___x_356_;
}
}
static lean_object* _init_l_Array_qsort___auto__1(void){
_start:
{
lean_object* v___x_357_; 
v___x_357_ = lean_obj_once(&l_Array_qsort___auto__1___closed__49, &l_Array_qsort___auto__1___closed__49_once, _init_l_Array_qsort___auto__1___closed__49);
return v___x_357_;
}
}
static lean_object* _init_l___private_Init_Data_Array_QSort_Basic_0__Array_qsort___auto__2(void){
_start:
{
lean_object* v___x_358_; 
v___x_358_ = lean_obj_once(&l_Array_qpartition___auto__1___closed__26, &l_Array_qpartition___auto__1___closed__26_once, _init_l_Array_qpartition___auto__1___closed__26);
return v___x_358_;
}
}
static lean_object* _init_l___private_Init_Data_Array_QSort_Basic_0__Array_qsort___auto__4(void){
_start:
{
lean_object* v___x_359_; 
v___x_359_ = lean_obj_once(&l_Array_qpartition___auto__1___closed__26, &l_Array_qpartition___auto__1___closed__26_once, _init_l_Array_qpartition___auto__1___closed__26);
return v___x_359_;
}
}
static lean_object* _init_l___private_Init_Data_Array_QSort_Basic_0__Array_qsort___auto__6(void){
_start:
{
lean_object* v___x_360_; 
v___x_360_ = lean_obj_once(&l_Array_qpartition___auto__1___closed__26, &l_Array_qpartition___auto__1___closed__26_once, _init_l_Array_qpartition___auto__1___closed__26);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___redArg(lean_object* v_lt_361_, lean_object* v_as_362_, lean_object* v_lo_363_, lean_object* v_hi_364_){
_start:
{
lean_object* v___y_366_; uint8_t v___x_376_; 
v___x_376_ = lean_nat_dec_lt(v_lo_363_, v_hi_364_);
if (v___x_376_ == 0)
{
lean_dec(v_lo_363_);
lean_dec_ref(v_lt_361_);
return v_as_362_;
}
else
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v_mid_379_; lean_object* v___y_381_; lean_object* v___y_388_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; uint8_t v___x_397_; 
v___x_377_ = lean_nat_add(v_lo_363_, v_hi_364_);
v___x_378_ = lean_unsigned_to_nat(1u);
v_mid_379_ = lean_nat_shiftr(v___x_377_, v___x_378_);
lean_dec(v___x_377_);
v___x_394_ = lean_array_fget_borrowed(v_as_362_, v_mid_379_);
v___x_395_ = lean_array_fget_borrowed(v_as_362_, v_lo_363_);
lean_inc_ref(v_lt_361_);
lean_inc(v___x_395_);
lean_inc(v___x_394_);
v___x_396_ = lean_apply_2(v_lt_361_, v___x_394_, v___x_395_);
v___x_397_ = lean_unbox(v___x_396_);
if (v___x_397_ == 0)
{
v___y_388_ = v_as_362_;
goto v___jp_387_;
}
else
{
lean_object* v___x_398_; 
v___x_398_ = lean_array_fswap(v_as_362_, v_lo_363_, v_mid_379_);
v___y_388_ = v___x_398_;
goto v___jp_387_;
}
v___jp_380_:
{
lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; uint8_t v___x_385_; 
v___x_382_ = lean_array_fget_borrowed(v___y_381_, v_mid_379_);
v___x_383_ = lean_array_fget_borrowed(v___y_381_, v_hi_364_);
lean_inc_ref(v_lt_361_);
lean_inc(v___x_383_);
lean_inc(v___x_382_);
v___x_384_ = lean_apply_2(v_lt_361_, v___x_382_, v___x_383_);
v___x_385_ = lean_unbox(v___x_384_);
if (v___x_385_ == 0)
{
lean_dec(v_mid_379_);
v___y_366_ = v___y_381_;
goto v___jp_365_;
}
else
{
lean_object* v___x_386_; 
v___x_386_ = lean_array_fswap(v___y_381_, v_mid_379_, v_hi_364_);
lean_dec(v_mid_379_);
v___y_366_ = v___x_386_;
goto v___jp_365_;
}
}
v___jp_387_:
{
lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; uint8_t v___x_392_; 
v___x_389_ = lean_array_fget_borrowed(v___y_388_, v_hi_364_);
v___x_390_ = lean_array_fget_borrowed(v___y_388_, v_lo_363_);
lean_inc_ref(v_lt_361_);
lean_inc(v___x_390_);
lean_inc(v___x_389_);
v___x_391_ = lean_apply_2(v_lt_361_, v___x_389_, v___x_390_);
v___x_392_ = lean_unbox(v___x_391_);
if (v___x_392_ == 0)
{
v___y_381_ = v___y_388_;
goto v___jp_380_;
}
else
{
lean_object* v___x_393_; 
v___x_393_ = lean_array_fswap(v___y_388_, v_lo_363_, v_hi_364_);
v___y_381_ = v___x_393_;
goto v___jp_380_;
}
}
}
v___jp_365_:
{
lean_object* v_pivot_367_; lean_object* v___x_368_; lean_object* v_fst_369_; lean_object* v_snd_370_; uint8_t v___x_371_; 
v_pivot_367_ = lean_array_fget(v___y_366_, v_hi_364_);
lean_inc_n(v_lo_363_, 2);
lean_inc_ref(v_lt_361_);
v___x_368_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___redArg(v_lt_361_, v_hi_364_, v_pivot_367_, v___y_366_, v_lo_363_, v_lo_363_);
v_fst_369_ = lean_ctor_get(v___x_368_, 0);
lean_inc(v_fst_369_);
v_snd_370_ = lean_ctor_get(v___x_368_, 1);
lean_inc(v_snd_370_);
lean_dec_ref(v___x_368_);
v___x_371_ = lean_nat_dec_le(v_hi_364_, v_fst_369_);
if (v___x_371_ == 0)
{
lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
lean_inc_ref(v_lt_361_);
v___x_372_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___redArg(v_lt_361_, v_snd_370_, v_lo_363_, v_fst_369_);
v___x_373_ = lean_unsigned_to_nat(1u);
v___x_374_ = lean_nat_add(v_fst_369_, v___x_373_);
lean_dec(v_fst_369_);
v_as_362_ = v___x_372_;
v_lo_363_ = v___x_374_;
goto _start;
}
else
{
lean_dec(v_fst_369_);
lean_dec(v_lo_363_);
lean_dec_ref(v_lt_361_);
return v_snd_370_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___redArg___boxed(lean_object* v_lt_399_, lean_object* v_as_400_, lean_object* v_lo_401_, lean_object* v_hi_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___redArg(v_lt_399_, v_as_400_, v_lo_401_, v_hi_402_);
lean_dec(v_hi_402_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_object* v_00_u03b1_404_, lean_object* v_lt_405_, lean_object* v_n_406_, lean_object* v_as_407_, lean_object* v_lo_408_, lean_object* v_hi_409_, lean_object* v_w_410_, lean_object* v_hlo_411_, lean_object* v_hhi_412_){
_start:
{
lean_object* v___x_413_; 
v___x_413_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___redArg(v_lt_405_, v_as_407_, v_lo_408_, v_hi_409_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___boxed(lean_object* v_00_u03b1_414_, lean_object* v_lt_415_, lean_object* v_n_416_, lean_object* v_as_417_, lean_object* v_lo_418_, lean_object* v_hi_419_, lean_object* v_w_420_, lean_object* v_hlo_421_, lean_object* v_hhi_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(v_00_u03b1_414_, v_lt_415_, v_n_416_, v_as_417_, v_lo_418_, v_hi_419_, v_w_420_, v_hlo_421_, v_hhi_422_);
lean_dec(v_hi_419_);
lean_dec(v_n_416_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_match__8_splitter___redArg(lean_object* v_x_424_, lean_object* v_h__1_425_){
_start:
{
lean_object* v_fst_426_; lean_object* v_snd_427_; lean_object* v___x_428_; 
v_fst_426_ = lean_ctor_get(v_x_424_, 0);
lean_inc(v_fst_426_);
v_snd_427_ = lean_ctor_get(v_x_424_, 1);
lean_inc(v_snd_427_);
lean_dec_ref(v_x_424_);
v___x_428_ = lean_apply_3(v_h__1_425_, v_fst_426_, lean_box(0), v_snd_427_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_match__8_splitter(lean_object* v_00_u03b1_429_, lean_object* v_n_430_, lean_object* v_lo_431_, lean_object* v_hi_432_, lean_object* v_motive_433_, lean_object* v_x_434_, lean_object* v_h__1_435_){
_start:
{
lean_object* v_fst_436_; lean_object* v_snd_437_; lean_object* v___x_438_; 
v_fst_436_ = lean_ctor_get(v_x_434_, 0);
lean_inc(v_fst_436_);
v_snd_437_ = lean_ctor_get(v_x_434_, 1);
lean_inc(v_snd_437_);
lean_dec_ref(v_x_434_);
v___x_438_ = lean_apply_3(v_h__1_435_, v_fst_436_, lean_box(0), v_snd_437_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_match__8_splitter___boxed(lean_object* v_00_u03b1_439_, lean_object* v_n_440_, lean_object* v_lo_441_, lean_object* v_hi_442_, lean_object* v_motive_443_, lean_object* v_x_444_, lean_object* v_h__1_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_match__8_splitter(v_00_u03b1_439_, v_n_440_, v_lo_441_, v_hi_442_, v_motive_443_, v_x_444_, v_h__1_445_);
lean_dec(v_hi_442_);
lean_dec(v_lo_441_);
lean_dec(v_n_440_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l_Array_qsort___redArg(lean_object* v_as_447_, lean_object* v_lt_448_, lean_object* v_lo_449_, lean_object* v_hi_450_){
_start:
{
lean_object* v___y_452_; lean_object* v___y_453_; lean_object* v___x_457_; lean_object* v___x_458_; uint8_t v___x_459_; 
v___x_457_ = lean_array_get_size(v_as_447_);
v___x_458_ = lean_unsigned_to_nat(0u);
v___x_459_ = lean_nat_dec_eq(v___x_457_, v___x_458_);
if (v___x_459_ == 0)
{
lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___y_463_; uint8_t v___x_465_; 
v___x_460_ = lean_unsigned_to_nat(1u);
v___x_461_ = lean_nat_sub(v___x_457_, v___x_460_);
v___x_465_ = lean_nat_dec_le(v_lo_449_, v___x_461_);
if (v___x_465_ == 0)
{
lean_dec(v_lo_449_);
lean_inc(v___x_461_);
v___y_463_ = v___x_461_;
goto v___jp_462_;
}
else
{
v___y_463_ = v_lo_449_;
goto v___jp_462_;
}
v___jp_462_:
{
uint8_t v___x_464_; 
v___x_464_ = lean_nat_dec_le(v_hi_450_, v___x_461_);
if (v___x_464_ == 0)
{
lean_dec(v_hi_450_);
v___y_452_ = v___y_463_;
v___y_453_ = v___x_461_;
goto v___jp_451_;
}
else
{
lean_dec(v___x_461_);
v___y_452_ = v___y_463_;
v___y_453_ = v_hi_450_;
goto v___jp_451_;
}
}
}
else
{
lean_dec(v_hi_450_);
lean_dec(v_lo_449_);
lean_dec_ref(v_lt_448_);
return v_as_447_;
}
v___jp_451_:
{
uint8_t v___x_454_; 
v___x_454_ = lean_nat_dec_le(v___y_452_, v___y_453_);
if (v___x_454_ == 0)
{
lean_object* v___x_455_; 
lean_dec(v___y_453_);
lean_inc(v___y_452_);
v___x_455_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___redArg(v_lt_448_, v_as_447_, v___y_452_, v___y_452_);
lean_dec(v___y_452_);
return v___x_455_;
}
else
{
lean_object* v___x_456_; 
v___x_456_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___redArg(v_lt_448_, v_as_447_, v___y_452_, v___y_453_);
lean_dec(v___y_453_);
return v___x_456_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_qsort(lean_object* v_00_u03b1_466_, lean_object* v_as_467_, lean_object* v_lt_468_, lean_object* v_lo_469_, lean_object* v_hi_470_){
_start:
{
lean_object* v___y_472_; lean_object* v___y_473_; lean_object* v___x_477_; lean_object* v___x_478_; uint8_t v___x_479_; 
v___x_477_ = lean_array_get_size(v_as_467_);
v___x_478_ = lean_unsigned_to_nat(0u);
v___x_479_ = lean_nat_dec_eq(v___x_477_, v___x_478_);
if (v___x_479_ == 0)
{
lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___y_483_; uint8_t v___x_485_; 
v___x_480_ = lean_unsigned_to_nat(1u);
v___x_481_ = lean_nat_sub(v___x_477_, v___x_480_);
v___x_485_ = lean_nat_dec_le(v_lo_469_, v___x_481_);
if (v___x_485_ == 0)
{
lean_dec(v_lo_469_);
lean_inc(v___x_481_);
v___y_483_ = v___x_481_;
goto v___jp_482_;
}
else
{
v___y_483_ = v_lo_469_;
goto v___jp_482_;
}
v___jp_482_:
{
uint8_t v___x_484_; 
v___x_484_ = lean_nat_dec_le(v_hi_470_, v___x_481_);
if (v___x_484_ == 0)
{
lean_dec(v_hi_470_);
v___y_472_ = v___y_483_;
v___y_473_ = v___x_481_;
goto v___jp_471_;
}
else
{
lean_dec(v___x_481_);
v___y_472_ = v___y_483_;
v___y_473_ = v_hi_470_;
goto v___jp_471_;
}
}
}
else
{
lean_dec(v_hi_470_);
lean_dec(v_lo_469_);
lean_dec_ref(v_lt_468_);
return v_as_467_;
}
v___jp_471_:
{
uint8_t v___x_474_; 
v___x_474_ = lean_nat_dec_le(v___y_472_, v___y_473_);
if (v___x_474_ == 0)
{
lean_object* v___x_475_; 
lean_dec(v___y_473_);
lean_inc(v___y_472_);
v___x_475_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___redArg(v_lt_468_, v_as_467_, v___y_472_, v___y_472_);
lean_dec(v___y_472_);
return v___x_475_;
}
else
{
lean_object* v___x_476_; 
v___x_476_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___redArg(v_lt_468_, v_as_467_, v___y_472_, v___y_473_);
lean_dec(v___y_473_);
return v___x_476_;
}
}
}
}
uint8_t l_Array_qsortOrd___redArg___lam__0(lean_object* v_ord_486_, uint8_t v___x_487_, lean_object* v_x_488_, lean_object* v_y_489_){
_start:
{
lean_object* v___x_490_; uint8_t v___x_491_; 
v___x_490_ = lean_apply_2(v_ord_486_, v_x_488_, v_y_489_);
v___x_491_ = lean_unbox(v___x_490_);
if (v___x_491_ == 0)
{
uint8_t v___x_492_; 
v___x_492_ = 1;
return v___x_492_;
}
else
{
return v___x_487_;
}
}
}
LEAN_EXPORT void l_Array_qsortOrd___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ord_486_ = stack[0].m_obj;
uint8_t v___x_487_ = stack[1].m_num;
lean_object* v_x_488_ = stack[2].m_obj;
lean_object* v_y_489_ = stack[3].m_obj;
uint8_t v_res_493_;
v_res_493_ = l_Array_qsortOrd___redArg___lam__0(v_ord_486_, v___x_487_, v_x_488_, v_y_489_);
stack->m_num = v_res_493_;
}
LEAN_EXPORT lean_object* l_Array_qsortOrd___redArg___lam__0___boxed(lean_object* v_ord_494_, lean_object* v___x_495_, lean_object* v_x_496_, lean_object* v_y_497_){
_start:
{
uint8_t v___x_66__boxed_498_; uint8_t v_res_499_; lean_object* v_r_500_; 
v___x_66__boxed_498_ = lean_unbox(v___x_495_);
v_res_499_ = l_Array_qsortOrd___redArg___lam__0(v_ord_494_, v___x_66__boxed_498_, v_x_496_, v_y_497_);
v_r_500_ = lean_box(v_res_499_);
return v_r_500_;
}
}
LEAN_EXPORT lean_object* l_Array_qsortOrd___redArg(lean_object* v_ord_501_, lean_object* v_xs_502_){
_start:
{
lean_object* v___x_503_; lean_object* v___x_504_; uint8_t v___x_505_; 
v___x_503_ = lean_array_get_size(v_xs_502_);
v___x_504_ = lean_unsigned_to_nat(0u);
v___x_505_ = lean_nat_dec_eq(v___x_503_, v___x_504_);
if (v___x_505_ == 0)
{
lean_object* v___x_506_; lean_object* v___f_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___y_511_; uint8_t v___x_515_; 
v___x_506_ = lean_box(v___x_505_);
v___f_507_ = lean_alloc_closure((void*)(l_Array_qsortOrd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_507_, 0, v_ord_501_);
lean_closure_set(v___f_507_, 1, v___x_506_);
v___x_508_ = lean_unsigned_to_nat(1u);
v___x_509_ = lean_nat_sub(v___x_503_, v___x_508_);
v___x_515_ = lean_nat_dec_le(v___x_504_, v___x_509_);
if (v___x_515_ == 0)
{
lean_inc(v___x_509_);
v___y_511_ = v___x_509_;
goto v___jp_510_;
}
else
{
v___y_511_ = v___x_504_;
goto v___jp_510_;
}
v___jp_510_:
{
uint8_t v___x_512_; 
v___x_512_ = lean_nat_dec_le(v___y_511_, v___x_509_);
if (v___x_512_ == 0)
{
lean_object* v___x_513_; 
lean_dec(v___x_509_);
lean_inc(v___y_511_);
v___x_513_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___redArg(v___f_507_, v_xs_502_, v___y_511_, v___y_511_);
lean_dec(v___y_511_);
return v___x_513_;
}
else
{
lean_object* v___x_514_; 
v___x_514_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___redArg(v___f_507_, v_xs_502_, v___y_511_, v___x_509_);
lean_dec(v___x_509_);
return v___x_514_;
}
}
}
else
{
lean_dec_ref(v_ord_501_);
return v_xs_502_;
}
}
}
LEAN_EXPORT lean_object* l_Array_qsortOrd(lean_object* v_00_u03b1_516_, lean_object* v_ord_517_, lean_object* v_xs_518_){
_start:
{
lean_object* v___x_519_; 
v___x_519_ = l_Array_qsortOrd___redArg(v_ord_517_, v_xs_518_);
return v___x_519_;
}
}
lean_object* runtime_initialize_Init_Data_Vector_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Ord_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Array_QSort_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Vector_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Ord_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Array_QSort_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Array_qpartition___auto__1 = _init_l_Array_qpartition___auto__1();
lean_mark_persistent(l_Array_qpartition___auto__1);
l_Array_qpartition___auto__3 = _init_l_Array_qpartition___auto__3();
lean_mark_persistent(l_Array_qpartition___auto__3);
l_Array_qpartition___auto__5 = _init_l_Array_qpartition___auto__5();
lean_mark_persistent(l_Array_qpartition___auto__5);
l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition___auto__2 = _init_l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition___auto__2();
lean_mark_persistent(l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition___auto__2);
l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition___auto__4 = _init_l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition___auto__4();
lean_mark_persistent(l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition___auto__4);
l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition___auto__6 = _init_l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition___auto__6();
lean_mark_persistent(l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition___auto__6);
l_Array_qsort___auto__1 = _init_l_Array_qsort___auto__1();
lean_mark_persistent(l_Array_qsort___auto__1);
l___private_Init_Data_Array_QSort_Basic_0__Array_qsort___auto__2 = _init_l___private_Init_Data_Array_QSort_Basic_0__Array_qsort___auto__2();
lean_mark_persistent(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort___auto__2);
l___private_Init_Data_Array_QSort_Basic_0__Array_qsort___auto__4 = _init_l___private_Init_Data_Array_QSort_Basic_0__Array_qsort___auto__4();
lean_mark_persistent(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort___auto__4);
l___private_Init_Data_Array_QSort_Basic_0__Array_qsort___auto__6 = _init_l___private_Init_Data_Array_QSort_Basic_0__Array_qsort___auto__6();
lean_mark_persistent(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort___auto__6);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Vector_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Ord_Basic(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Array_QSort_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Vector_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Ord_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_QSort_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Array_QSort_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Array_QSort_Basic(builtin);
}
#ifdef __cplusplus
}
#endif

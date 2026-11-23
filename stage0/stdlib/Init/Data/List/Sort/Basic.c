// Lean compiler output
// Module: Init.Data.List.Sort.Basic
// Imports: public import Init.Ext import Init.Data.List.Nat.TakeDrop import Init.Data.List.TakeDrop import Init.Data.Nat.Lemmas import Init.Omega
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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_List_splitAt___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
static const lean_string_object l_List_merge___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_List_merge___auto__1___closed__0 = (const lean_object*)&l_List_merge___auto__1___closed__0_value;
static const lean_string_object l_List_merge___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_List_merge___auto__1___closed__1 = (const lean_object*)&l_List_merge___auto__1___closed__1_value;
static const lean_string_object l_List_merge___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_List_merge___auto__1___closed__2 = (const lean_object*)&l_List_merge___auto__1___closed__2_value;
static const lean_string_object l_List_merge___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_List_merge___auto__1___closed__3 = (const lean_object*)&l_List_merge___auto__1___closed__3_value;
static const lean_ctor_object l_List_merge___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_merge___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_merge___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_merge___auto__1___closed__4_value_aux_0),((lean_object*)&l_List_merge___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_merge___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_merge___auto__1___closed__4_value_aux_1),((lean_object*)&l_List_merge___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_List_merge___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_merge___auto__1___closed__4_value_aux_2),((lean_object*)&l_List_merge___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_List_merge___auto__1___closed__4 = (const lean_object*)&l_List_merge___auto__1___closed__4_value;
static const lean_array_object l_List_merge___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_List_merge___auto__1___closed__5 = (const lean_object*)&l_List_merge___auto__1___closed__5_value;
static const lean_string_object l_List_merge___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_List_merge___auto__1___closed__6 = (const lean_object*)&l_List_merge___auto__1___closed__6_value;
static const lean_ctor_object l_List_merge___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_merge___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_merge___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_merge___auto__1___closed__7_value_aux_0),((lean_object*)&l_List_merge___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_merge___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_merge___auto__1___closed__7_value_aux_1),((lean_object*)&l_List_merge___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_List_merge___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_merge___auto__1___closed__7_value_aux_2),((lean_object*)&l_List_merge___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_List_merge___auto__1___closed__7 = (const lean_object*)&l_List_merge___auto__1___closed__7_value;
static const lean_string_object l_List_merge___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_List_merge___auto__1___closed__8 = (const lean_object*)&l_List_merge___auto__1___closed__8_value;
static const lean_ctor_object l_List_merge___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_merge___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_List_merge___auto__1___closed__9 = (const lean_object*)&l_List_merge___auto__1___closed__9_value;
static const lean_string_object l_List_merge___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l_List_merge___auto__1___closed__10 = (const lean_object*)&l_List_merge___auto__1___closed__10_value;
static const lean_ctor_object l_List_merge___auto__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_merge___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_merge___auto__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_merge___auto__1___closed__11_value_aux_0),((lean_object*)&l_List_merge___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_merge___auto__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_merge___auto__1___closed__11_value_aux_1),((lean_object*)&l_List_merge___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_List_merge___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_merge___auto__1___closed__11_value_aux_2),((lean_object*)&l_List_merge___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l_List_merge___auto__1___closed__11 = (const lean_object*)&l_List_merge___auto__1___closed__11_value;
static lean_once_cell_t l_List_merge___auto__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_merge___auto__1___closed__12;
static lean_once_cell_t l_List_merge___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_merge___auto__1___closed__13;
static const lean_string_object l_List_merge___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_List_merge___auto__1___closed__14 = (const lean_object*)&l_List_merge___auto__1___closed__14_value;
static const lean_string_object l_List_merge___auto__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fun"};
static const lean_object* l_List_merge___auto__1___closed__15 = (const lean_object*)&l_List_merge___auto__1___closed__15_value;
static const lean_ctor_object l_List_merge___auto__1___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_merge___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_merge___auto__1___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_merge___auto__1___closed__16_value_aux_0),((lean_object*)&l_List_merge___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_merge___auto__1___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_merge___auto__1___closed__16_value_aux_1),((lean_object*)&l_List_merge___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_List_merge___auto__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_merge___auto__1___closed__16_value_aux_2),((lean_object*)&l_List_merge___auto__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(249, 155, 133, 242, 71, 132, 191, 97)}};
static const lean_object* l_List_merge___auto__1___closed__16 = (const lean_object*)&l_List_merge___auto__1___closed__16_value;
static lean_once_cell_t l_List_merge___auto__1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_merge___auto__1___closed__17;
static lean_once_cell_t l_List_merge___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_merge___auto__1___closed__18;
static const lean_string_object l_List_merge___auto__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "basicFun"};
static const lean_object* l_List_merge___auto__1___closed__19 = (const lean_object*)&l_List_merge___auto__1___closed__19_value;
static const lean_ctor_object l_List_merge___auto__1___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_merge___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_merge___auto__1___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_merge___auto__1___closed__20_value_aux_0),((lean_object*)&l_List_merge___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_merge___auto__1___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_merge___auto__1___closed__20_value_aux_1),((lean_object*)&l_List_merge___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_List_merge___auto__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_merge___auto__1___closed__20_value_aux_2),((lean_object*)&l_List_merge___auto__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(209, 134, 40, 160, 122, 195, 31, 223)}};
static const lean_object* l_List_merge___auto__1___closed__20 = (const lean_object*)&l_List_merge___auto__1___closed__20_value;
static const lean_string_object l_List_merge___auto__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "a"};
static const lean_object* l_List_merge___auto__1___closed__21 = (const lean_object*)&l_List_merge___auto__1___closed__21_value;
static const lean_ctor_object l_List_merge___auto__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_List_merge___auto__1___closed__21_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_List_merge___auto__1___closed__22 = (const lean_object*)&l_List_merge___auto__1___closed__22_value;
static const lean_ctor_object l_List_merge___auto__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_merge___auto__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(247, 80, 99, 121, 74, 33, 203, 108)}};
static const lean_object* l_List_merge___auto__1___closed__23 = (const lean_object*)&l_List_merge___auto__1___closed__23_value;
static const lean_ctor_object l_List_merge___auto__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 3}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_List_merge___auto__1___closed__22_value),((lean_object*)&l_List_merge___auto__1___closed__23_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_merge___auto__1___closed__24 = (const lean_object*)&l_List_merge___auto__1___closed__24_value;
static lean_once_cell_t l_List_merge___auto__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_merge___auto__1___closed__25;
static const lean_string_object l_List_merge___auto__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "b"};
static const lean_object* l_List_merge___auto__1___closed__26 = (const lean_object*)&l_List_merge___auto__1___closed__26_value;
static const lean_ctor_object l_List_merge___auto__1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_List_merge___auto__1___closed__26_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_List_merge___auto__1___closed__27 = (const lean_object*)&l_List_merge___auto__1___closed__27_value;
static const lean_ctor_object l_List_merge___auto__1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_merge___auto__1___closed__26_value),LEAN_SCALAR_PTR_LITERAL(47, 22, 244, 233, 226, 169, 241, 142)}};
static const lean_object* l_List_merge___auto__1___closed__28 = (const lean_object*)&l_List_merge___auto__1___closed__28_value;
static const lean_ctor_object l_List_merge___auto__1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 3}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_List_merge___auto__1___closed__27_value),((lean_object*)&l_List_merge___auto__1___closed__28_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_merge___auto__1___closed__29 = (const lean_object*)&l_List_merge___auto__1___closed__29_value;
static lean_once_cell_t l_List_merge___auto__1___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_merge___auto__1___closed__30;
static lean_once_cell_t l_List_merge___auto__1___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_merge___auto__1___closed__31;
static lean_once_cell_t l_List_merge___auto__1___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_merge___auto__1___closed__32;
static const lean_ctor_object l_List_merge___auto__1___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_List_merge___auto__1___closed__9_value),((lean_object*)&l_List_merge___auto__1___closed__5_value)}};
static const lean_object* l_List_merge___auto__1___closed__33 = (const lean_object*)&l_List_merge___auto__1___closed__33_value;
static lean_once_cell_t l_List_merge___auto__1___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_merge___auto__1___closed__34;
static const lean_string_object l_List_merge___auto__1___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l_List_merge___auto__1___closed__35 = (const lean_object*)&l_List_merge___auto__1___closed__35_value;
static lean_once_cell_t l_List_merge___auto__1___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_merge___auto__1___closed__36;
static lean_once_cell_t l_List_merge___auto__1___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_merge___auto__1___closed__37;
static const lean_string_object l_List_merge___auto__1___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 7, .m_data = "term_≤_"};
static const lean_object* l_List_merge___auto__1___closed__38 = (const lean_object*)&l_List_merge___auto__1___closed__38_value;
static const lean_ctor_object l_List_merge___auto__1___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_merge___auto__1___closed__38_value),LEAN_SCALAR_PTR_LITERAL(111, 3, 61, 112, 38, 138, 106, 121)}};
static const lean_object* l_List_merge___auto__1___closed__39 = (const lean_object*)&l_List_merge___auto__1___closed__39_value;
static const lean_string_object l_List_merge___auto__1___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "≤"};
static const lean_object* l_List_merge___auto__1___closed__40 = (const lean_object*)&l_List_merge___auto__1___closed__40_value;
static lean_once_cell_t l_List_merge___auto__1___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_merge___auto__1___closed__41;
static lean_once_cell_t l_List_merge___auto__1___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_merge___auto__1___closed__42;
static lean_once_cell_t l_List_merge___auto__1___closed__43_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_merge___auto__1___closed__43;
static lean_once_cell_t l_List_merge___auto__1___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_merge___auto__1___closed__44;
static lean_once_cell_t l_List_merge___auto__1___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_merge___auto__1___closed__45;
static lean_once_cell_t l_List_merge___auto__1___closed__46_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_merge___auto__1___closed__46;
static lean_once_cell_t l_List_merge___auto__1___closed__47_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_merge___auto__1___closed__47;
static lean_once_cell_t l_List_merge___auto__1___closed__48_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_merge___auto__1___closed__48;
static lean_once_cell_t l_List_merge___auto__1___closed__49_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_merge___auto__1___closed__49;
static lean_once_cell_t l_List_merge___auto__1___closed__50_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_merge___auto__1___closed__50;
static lean_once_cell_t l_List_merge___auto__1___closed__51_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_merge___auto__1___closed__51;
static lean_once_cell_t l_List_merge___auto__1___closed__52_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_merge___auto__1___closed__52;
static lean_once_cell_t l_List_merge___auto__1___closed__53_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_merge___auto__1___closed__53;
static lean_once_cell_t l_List_merge___auto__1___closed__54_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_merge___auto__1___closed__54;
static lean_once_cell_t l_List_merge___auto__1___closed__55_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_merge___auto__1___closed__55;
static lean_once_cell_t l_List_merge___auto__1___closed__56_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_merge___auto__1___closed__56;
LEAN_EXPORT lean_object* l_List_merge___auto__1;
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Basic_0__List_merge_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Basic_0__List_merge_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_splitInTwo___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_splitInTwo___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_splitInTwo(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_splitInTwo___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mergeSort___auto__1;
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Basic_0__List_mergeSort_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Basic_0__List_mergeSort_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_zipIdxLE___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_zipIdxLE___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_zipIdxLE(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_zipIdxLE___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_List_merge___auto__1___closed__12(void){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_27_ = ((lean_object*)(l_List_merge___auto__1___closed__10));
v___x_28_ = l_Lean_mkAtom(v___x_27_);
return v___x_28_;
}
}
static lean_object* _init_l_List_merge___auto__1___closed__13(void){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_29_ = lean_obj_once(&l_List_merge___auto__1___closed__12, &l_List_merge___auto__1___closed__12_once, _init_l_List_merge___auto__1___closed__12);
v___x_30_ = ((lean_object*)(l_List_merge___auto__1___closed__5));
v___x_31_ = lean_array_push(v___x_30_, v___x_29_);
return v___x_31_;
}
}
static lean_object* _init_l_List_merge___auto__1___closed__17(void){
_start:
{
lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_39_ = ((lean_object*)(l_List_merge___auto__1___closed__15));
v___x_40_ = l_Lean_mkAtom(v___x_39_);
return v___x_40_;
}
}
static lean_object* _init_l_List_merge___auto__1___closed__18(void){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_41_ = lean_obj_once(&l_List_merge___auto__1___closed__17, &l_List_merge___auto__1___closed__17_once, _init_l_List_merge___auto__1___closed__17);
v___x_42_ = ((lean_object*)(l_List_merge___auto__1___closed__5));
v___x_43_ = lean_array_push(v___x_42_, v___x_41_);
return v___x_43_;
}
}
static lean_object* _init_l_List_merge___auto__1___closed__25(void){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_62_ = ((lean_object*)(l_List_merge___auto__1___closed__24));
v___x_63_ = ((lean_object*)(l_List_merge___auto__1___closed__5));
v___x_64_ = lean_array_push(v___x_63_, v___x_62_);
return v___x_64_;
}
}
static lean_object* _init_l_List_merge___auto__1___closed__30(void){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_77_ = ((lean_object*)(l_List_merge___auto__1___closed__29));
v___x_78_ = lean_obj_once(&l_List_merge___auto__1___closed__25, &l_List_merge___auto__1___closed__25_once, _init_l_List_merge___auto__1___closed__25);
v___x_79_ = lean_array_push(v___x_78_, v___x_77_);
return v___x_79_;
}
}
static lean_object* _init_l_List_merge___auto__1___closed__31(void){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_80_ = lean_obj_once(&l_List_merge___auto__1___closed__30, &l_List_merge___auto__1___closed__30_once, _init_l_List_merge___auto__1___closed__30);
v___x_81_ = ((lean_object*)(l_List_merge___auto__1___closed__9));
v___x_82_ = lean_box(2);
v___x_83_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_83_, 0, v___x_82_);
lean_ctor_set(v___x_83_, 1, v___x_81_);
lean_ctor_set(v___x_83_, 2, v___x_80_);
return v___x_83_;
}
}
static lean_object* _init_l_List_merge___auto__1___closed__32(void){
_start:
{
lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_84_ = lean_obj_once(&l_List_merge___auto__1___closed__31, &l_List_merge___auto__1___closed__31_once, _init_l_List_merge___auto__1___closed__31);
v___x_85_ = ((lean_object*)(l_List_merge___auto__1___closed__5));
v___x_86_ = lean_array_push(v___x_85_, v___x_84_);
return v___x_86_;
}
}
static lean_object* _init_l_List_merge___auto__1___closed__34(void){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_91_ = ((lean_object*)(l_List_merge___auto__1___closed__33));
v___x_92_ = lean_obj_once(&l_List_merge___auto__1___closed__32, &l_List_merge___auto__1___closed__32_once, _init_l_List_merge___auto__1___closed__32);
v___x_93_ = lean_array_push(v___x_92_, v___x_91_);
return v___x_93_;
}
}
static lean_object* _init_l_List_merge___auto__1___closed__36(void){
_start:
{
lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_95_ = ((lean_object*)(l_List_merge___auto__1___closed__35));
v___x_96_ = l_Lean_mkAtom(v___x_95_);
return v___x_96_;
}
}
static lean_object* _init_l_List_merge___auto__1___closed__37(void){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_97_ = lean_obj_once(&l_List_merge___auto__1___closed__36, &l_List_merge___auto__1___closed__36_once, _init_l_List_merge___auto__1___closed__36);
v___x_98_ = lean_obj_once(&l_List_merge___auto__1___closed__34, &l_List_merge___auto__1___closed__34_once, _init_l_List_merge___auto__1___closed__34);
v___x_99_ = lean_array_push(v___x_98_, v___x_97_);
return v___x_99_;
}
}
static lean_object* _init_l_List_merge___auto__1___closed__41(void){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_104_ = ((lean_object*)(l_List_merge___auto__1___closed__40));
v___x_105_ = l_Lean_mkAtom(v___x_104_);
return v___x_105_;
}
}
static lean_object* _init_l_List_merge___auto__1___closed__42(void){
_start:
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_106_ = lean_obj_once(&l_List_merge___auto__1___closed__41, &l_List_merge___auto__1___closed__41_once, _init_l_List_merge___auto__1___closed__41);
v___x_107_ = lean_obj_once(&l_List_merge___auto__1___closed__25, &l_List_merge___auto__1___closed__25_once, _init_l_List_merge___auto__1___closed__25);
v___x_108_ = lean_array_push(v___x_107_, v___x_106_);
return v___x_108_;
}
}
static lean_object* _init_l_List_merge___auto__1___closed__43(void){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_109_ = ((lean_object*)(l_List_merge___auto__1___closed__29));
v___x_110_ = lean_obj_once(&l_List_merge___auto__1___closed__42, &l_List_merge___auto__1___closed__42_once, _init_l_List_merge___auto__1___closed__42);
v___x_111_ = lean_array_push(v___x_110_, v___x_109_);
return v___x_111_;
}
}
static lean_object* _init_l_List_merge___auto__1___closed__44(void){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_112_ = lean_obj_once(&l_List_merge___auto__1___closed__43, &l_List_merge___auto__1___closed__43_once, _init_l_List_merge___auto__1___closed__43);
v___x_113_ = ((lean_object*)(l_List_merge___auto__1___closed__39));
v___x_114_ = lean_box(2);
v___x_115_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_115_, 0, v___x_114_);
lean_ctor_set(v___x_115_, 1, v___x_113_);
lean_ctor_set(v___x_115_, 2, v___x_112_);
return v___x_115_;
}
}
static lean_object* _init_l_List_merge___auto__1___closed__45(void){
_start:
{
lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_116_ = lean_obj_once(&l_List_merge___auto__1___closed__44, &l_List_merge___auto__1___closed__44_once, _init_l_List_merge___auto__1___closed__44);
v___x_117_ = lean_obj_once(&l_List_merge___auto__1___closed__37, &l_List_merge___auto__1___closed__37_once, _init_l_List_merge___auto__1___closed__37);
v___x_118_ = lean_array_push(v___x_117_, v___x_116_);
return v___x_118_;
}
}
static lean_object* _init_l_List_merge___auto__1___closed__46(void){
_start:
{
lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_119_ = lean_obj_once(&l_List_merge___auto__1___closed__45, &l_List_merge___auto__1___closed__45_once, _init_l_List_merge___auto__1___closed__45);
v___x_120_ = ((lean_object*)(l_List_merge___auto__1___closed__20));
v___x_121_ = lean_box(2);
v___x_122_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_122_, 0, v___x_121_);
lean_ctor_set(v___x_122_, 1, v___x_120_);
lean_ctor_set(v___x_122_, 2, v___x_119_);
return v___x_122_;
}
}
static lean_object* _init_l_List_merge___auto__1___closed__47(void){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_123_ = lean_obj_once(&l_List_merge___auto__1___closed__46, &l_List_merge___auto__1___closed__46_once, _init_l_List_merge___auto__1___closed__46);
v___x_124_ = lean_obj_once(&l_List_merge___auto__1___closed__18, &l_List_merge___auto__1___closed__18_once, _init_l_List_merge___auto__1___closed__18);
v___x_125_ = lean_array_push(v___x_124_, v___x_123_);
return v___x_125_;
}
}
static lean_object* _init_l_List_merge___auto__1___closed__48(void){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_126_ = lean_obj_once(&l_List_merge___auto__1___closed__47, &l_List_merge___auto__1___closed__47_once, _init_l_List_merge___auto__1___closed__47);
v___x_127_ = ((lean_object*)(l_List_merge___auto__1___closed__16));
v___x_128_ = lean_box(2);
v___x_129_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_129_, 0, v___x_128_);
lean_ctor_set(v___x_129_, 1, v___x_127_);
lean_ctor_set(v___x_129_, 2, v___x_126_);
return v___x_129_;
}
}
static lean_object* _init_l_List_merge___auto__1___closed__49(void){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_130_ = lean_obj_once(&l_List_merge___auto__1___closed__48, &l_List_merge___auto__1___closed__48_once, _init_l_List_merge___auto__1___closed__48);
v___x_131_ = lean_obj_once(&l_List_merge___auto__1___closed__13, &l_List_merge___auto__1___closed__13_once, _init_l_List_merge___auto__1___closed__13);
v___x_132_ = lean_array_push(v___x_131_, v___x_130_);
return v___x_132_;
}
}
static lean_object* _init_l_List_merge___auto__1___closed__50(void){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_133_ = lean_obj_once(&l_List_merge___auto__1___closed__49, &l_List_merge___auto__1___closed__49_once, _init_l_List_merge___auto__1___closed__49);
v___x_134_ = ((lean_object*)(l_List_merge___auto__1___closed__11));
v___x_135_ = lean_box(2);
v___x_136_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_136_, 0, v___x_135_);
lean_ctor_set(v___x_136_, 1, v___x_134_);
lean_ctor_set(v___x_136_, 2, v___x_133_);
return v___x_136_;
}
}
static lean_object* _init_l_List_merge___auto__1___closed__51(void){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_137_ = lean_obj_once(&l_List_merge___auto__1___closed__50, &l_List_merge___auto__1___closed__50_once, _init_l_List_merge___auto__1___closed__50);
v___x_138_ = ((lean_object*)(l_List_merge___auto__1___closed__5));
v___x_139_ = lean_array_push(v___x_138_, v___x_137_);
return v___x_139_;
}
}
static lean_object* _init_l_List_merge___auto__1___closed__52(void){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_140_ = lean_obj_once(&l_List_merge___auto__1___closed__51, &l_List_merge___auto__1___closed__51_once, _init_l_List_merge___auto__1___closed__51);
v___x_141_ = ((lean_object*)(l_List_merge___auto__1___closed__9));
v___x_142_ = lean_box(2);
v___x_143_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_143_, 0, v___x_142_);
lean_ctor_set(v___x_143_, 1, v___x_141_);
lean_ctor_set(v___x_143_, 2, v___x_140_);
return v___x_143_;
}
}
static lean_object* _init_l_List_merge___auto__1___closed__53(void){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_144_ = lean_obj_once(&l_List_merge___auto__1___closed__52, &l_List_merge___auto__1___closed__52_once, _init_l_List_merge___auto__1___closed__52);
v___x_145_ = ((lean_object*)(l_List_merge___auto__1___closed__5));
v___x_146_ = lean_array_push(v___x_145_, v___x_144_);
return v___x_146_;
}
}
static lean_object* _init_l_List_merge___auto__1___closed__54(void){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_147_ = lean_obj_once(&l_List_merge___auto__1___closed__53, &l_List_merge___auto__1___closed__53_once, _init_l_List_merge___auto__1___closed__53);
v___x_148_ = ((lean_object*)(l_List_merge___auto__1___closed__7));
v___x_149_ = lean_box(2);
v___x_150_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_150_, 0, v___x_149_);
lean_ctor_set(v___x_150_, 1, v___x_148_);
lean_ctor_set(v___x_150_, 2, v___x_147_);
return v___x_150_;
}
}
static lean_object* _init_l_List_merge___auto__1___closed__55(void){
_start:
{
lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_151_ = lean_obj_once(&l_List_merge___auto__1___closed__54, &l_List_merge___auto__1___closed__54_once, _init_l_List_merge___auto__1___closed__54);
v___x_152_ = ((lean_object*)(l_List_merge___auto__1___closed__5));
v___x_153_ = lean_array_push(v___x_152_, v___x_151_);
return v___x_153_;
}
}
static lean_object* _init_l_List_merge___auto__1___closed__56(void){
_start:
{
lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_154_ = lean_obj_once(&l_List_merge___auto__1___closed__55, &l_List_merge___auto__1___closed__55_once, _init_l_List_merge___auto__1___closed__55);
v___x_155_ = ((lean_object*)(l_List_merge___auto__1___closed__4));
v___x_156_ = lean_box(2);
v___x_157_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_157_, 0, v___x_156_);
lean_ctor_set(v___x_157_, 1, v___x_155_);
lean_ctor_set(v___x_157_, 2, v___x_154_);
return v___x_157_;
}
}
static lean_object* _init_l_List_merge___auto__1(void){
_start:
{
lean_object* v___x_158_; 
v___x_158_ = lean_obj_once(&l_List_merge___auto__1___closed__56, &l_List_merge___auto__1___closed__56_once, _init_l_List_merge___auto__1___closed__56);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Basic_0__List_merge_match__1_splitter___redArg(lean_object* v_xs_159_, lean_object* v_ys_160_, lean_object* v_h__1_161_, lean_object* v_h__2_162_, lean_object* v_h__3_163_){
_start:
{
if (lean_obj_tag(v_xs_159_) == 0)
{
lean_object* v___x_164_; 
lean_dec(v_h__3_163_);
lean_dec(v_h__2_162_);
v___x_164_ = lean_apply_1(v_h__1_161_, v_ys_160_);
return v___x_164_;
}
else
{
lean_dec(v_h__1_161_);
if (lean_obj_tag(v_ys_160_) == 0)
{
lean_object* v___x_165_; 
lean_dec(v_h__3_163_);
v___x_165_ = lean_apply_2(v_h__2_162_, v_xs_159_, lean_box(0));
return v___x_165_;
}
else
{
lean_object* v_head_166_; lean_object* v_tail_167_; lean_object* v_head_168_; lean_object* v_tail_169_; lean_object* v___x_170_; 
lean_dec(v_h__2_162_);
v_head_166_ = lean_ctor_get(v_xs_159_, 0);
lean_inc(v_head_166_);
v_tail_167_ = lean_ctor_get(v_xs_159_, 1);
lean_inc(v_tail_167_);
lean_dec_ref_known(v_xs_159_, 2);
v_head_168_ = lean_ctor_get(v_ys_160_, 0);
lean_inc(v_head_168_);
v_tail_169_ = lean_ctor_get(v_ys_160_, 1);
lean_inc(v_tail_169_);
lean_dec_ref_known(v_ys_160_, 2);
v___x_170_ = lean_apply_4(v_h__3_163_, v_head_166_, v_tail_167_, v_head_168_, v_tail_169_);
return v___x_170_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Basic_0__List_merge_match__1_splitter(lean_object* v_00_u03b1_171_, lean_object* v_motive_172_, lean_object* v_xs_173_, lean_object* v_ys_174_, lean_object* v_h__1_175_, lean_object* v_h__2_176_, lean_object* v_h__3_177_){
_start:
{
if (lean_obj_tag(v_xs_173_) == 0)
{
lean_object* v___x_178_; 
lean_dec(v_h__3_177_);
lean_dec(v_h__2_176_);
v___x_178_ = lean_apply_1(v_h__1_175_, v_ys_174_);
return v___x_178_;
}
else
{
lean_dec(v_h__1_175_);
if (lean_obj_tag(v_ys_174_) == 0)
{
lean_object* v___x_179_; 
lean_dec(v_h__3_177_);
v___x_179_ = lean_apply_2(v_h__2_176_, v_xs_173_, lean_box(0));
return v___x_179_;
}
else
{
lean_object* v_head_180_; lean_object* v_tail_181_; lean_object* v_head_182_; lean_object* v_tail_183_; lean_object* v___x_184_; 
lean_dec(v_h__2_176_);
v_head_180_ = lean_ctor_get(v_xs_173_, 0);
lean_inc(v_head_180_);
v_tail_181_ = lean_ctor_get(v_xs_173_, 1);
lean_inc(v_tail_181_);
lean_dec_ref_known(v_xs_173_, 2);
v_head_182_ = lean_ctor_get(v_ys_174_, 0);
lean_inc(v_head_182_);
v_tail_183_ = lean_ctor_get(v_ys_174_, 1);
lean_inc(v_tail_183_);
lean_dec_ref_known(v_ys_174_, 2);
v___x_184_ = lean_apply_4(v_h__3_177_, v_head_180_, v_tail_181_, v_head_182_, v_tail_183_);
return v___x_184_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_splitInTwo___redArg(lean_object* v_n_185_, lean_object* v_l_186_){
_start:
{
lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v_r_190_; lean_object* v_fst_191_; lean_object* v_snd_192_; lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_199_; 
v___x_187_ = lean_unsigned_to_nat(1u);
v___x_188_ = lean_nat_add(v_n_185_, v___x_187_);
v___x_189_ = lean_nat_shiftr(v___x_188_, v___x_187_);
lean_dec(v___x_188_);
v_r_190_ = l_List_splitAt___redArg(v___x_189_, v_l_186_);
v_fst_191_ = lean_ctor_get(v_r_190_, 0);
v_snd_192_ = lean_ctor_get(v_r_190_, 1);
v_isSharedCheck_199_ = !lean_is_exclusive(v_r_190_);
if (v_isSharedCheck_199_ == 0)
{
v___x_194_ = v_r_190_;
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
else
{
lean_inc(v_snd_192_);
lean_inc(v_fst_191_);
lean_dec(v_r_190_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
lean_object* v___x_197_; 
if (v_isShared_195_ == 0)
{
v___x_197_ = v___x_194_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v_fst_191_);
lean_ctor_set(v_reuseFailAlloc_198_, 1, v_snd_192_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
return v___x_197_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_splitInTwo___redArg___boxed(lean_object* v_n_200_, lean_object* v_l_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l_List_MergeSort_Internal_splitInTwo___redArg(v_n_200_, v_l_201_);
lean_dec(v_n_200_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_splitInTwo(lean_object* v_00_u03b1_203_, lean_object* v_n_204_, lean_object* v_l_205_){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = l_List_MergeSort_Internal_splitInTwo___redArg(v_n_204_, v_l_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_splitInTwo___boxed(lean_object* v_00_u03b1_207_, lean_object* v_n_208_, lean_object* v_l_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_List_MergeSort_Internal_splitInTwo(v_00_u03b1_207_, v_n_208_, v_l_209_);
lean_dec(v_n_208_);
return v_res_210_;
}
}
static lean_object* _init_l_List_mergeSort___auto__1(void){
_start:
{
lean_object* v___x_211_; 
v___x_211_ = lean_obj_once(&l_List_merge___auto__1___closed__56, &l_List_merge___auto__1___closed__56_once, _init_l_List_merge___auto__1___closed__56);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Basic_0__List_mergeSort_match__1_splitter___redArg(lean_object* v_x_212_, lean_object* v_x_213_, lean_object* v_h__1_214_, lean_object* v_h__2_215_, lean_object* v_h__3_216_){
_start:
{
if (lean_obj_tag(v_x_212_) == 0)
{
lean_object* v___x_217_; 
lean_dec(v_h__3_216_);
lean_dec(v_h__2_215_);
v___x_217_ = lean_apply_1(v_h__1_214_, v_x_213_);
return v___x_217_;
}
else
{
lean_object* v_tail_218_; 
lean_dec(v_h__1_214_);
v_tail_218_ = lean_ctor_get(v_x_212_, 1);
if (lean_obj_tag(v_tail_218_) == 0)
{
lean_object* v_head_219_; lean_object* v___x_220_; 
lean_dec(v_h__3_216_);
v_head_219_ = lean_ctor_get(v_x_212_, 0);
lean_inc(v_head_219_);
lean_dec_ref_known(v_x_212_, 2);
v___x_220_ = lean_apply_2(v_h__2_215_, v_head_219_, v_x_213_);
return v___x_220_;
}
else
{
lean_object* v_head_221_; lean_object* v_head_222_; lean_object* v_tail_223_; lean_object* v___x_224_; 
lean_inc_ref(v_tail_218_);
lean_dec(v_h__2_215_);
v_head_221_ = lean_ctor_get(v_x_212_, 0);
lean_inc(v_head_221_);
lean_dec_ref_known(v_x_212_, 2);
v_head_222_ = lean_ctor_get(v_tail_218_, 0);
lean_inc(v_head_222_);
v_tail_223_ = lean_ctor_get(v_tail_218_, 1);
lean_inc(v_tail_223_);
lean_dec_ref_known(v_tail_218_, 2);
v___x_224_ = lean_apply_4(v_h__3_216_, v_head_221_, v_head_222_, v_tail_223_, v_x_213_);
return v___x_224_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Basic_0__List_mergeSort_match__1_splitter(lean_object* v_00_u03b1_225_, lean_object* v_motive_226_, lean_object* v_x_227_, lean_object* v_x_228_, lean_object* v_h__1_229_, lean_object* v_h__2_230_, lean_object* v_h__3_231_){
_start:
{
if (lean_obj_tag(v_x_227_) == 0)
{
lean_object* v___x_232_; 
lean_dec(v_h__3_231_);
lean_dec(v_h__2_230_);
v___x_232_ = lean_apply_1(v_h__1_229_, v_x_228_);
return v___x_232_;
}
else
{
lean_object* v_tail_233_; 
lean_dec(v_h__1_229_);
v_tail_233_ = lean_ctor_get(v_x_227_, 1);
if (lean_obj_tag(v_tail_233_) == 0)
{
lean_object* v_head_234_; lean_object* v___x_235_; 
lean_dec(v_h__3_231_);
v_head_234_ = lean_ctor_get(v_x_227_, 0);
lean_inc(v_head_234_);
lean_dec_ref_known(v_x_227_, 2);
v___x_235_ = lean_apply_2(v_h__2_230_, v_head_234_, v_x_228_);
return v___x_235_;
}
else
{
lean_object* v_head_236_; lean_object* v_head_237_; lean_object* v_tail_238_; lean_object* v___x_239_; 
lean_inc_ref(v_tail_233_);
lean_dec(v_h__2_230_);
v_head_236_ = lean_ctor_get(v_x_227_, 0);
lean_inc(v_head_236_);
lean_dec_ref_known(v_x_227_, 2);
v_head_237_ = lean_ctor_get(v_tail_233_, 0);
lean_inc(v_head_237_);
v_tail_238_ = lean_ctor_get(v_tail_233_, 1);
lean_inc(v_tail_238_);
lean_dec_ref_known(v_tail_233_, 2);
v___x_239_ = lean_apply_4(v_h__3_231_, v_head_236_, v_head_237_, v_tail_238_, v_x_228_);
return v___x_239_;
}
}
}
}
LEAN_EXPORT uint8_t l_List_zipIdxLE___redArg(lean_object* v_le_240_, lean_object* v_a_241_, lean_object* v_b_242_){
_start:
{
lean_object* v_fst_243_; lean_object* v_snd_244_; lean_object* v_fst_245_; lean_object* v_snd_246_; lean_object* v___x_247_; uint8_t v___x_248_; 
v_fst_243_ = lean_ctor_get(v_a_241_, 0);
lean_inc_n(v_fst_243_, 2);
v_snd_244_ = lean_ctor_get(v_a_241_, 1);
lean_inc(v_snd_244_);
lean_dec_ref(v_a_241_);
v_fst_245_ = lean_ctor_get(v_b_242_, 0);
lean_inc_n(v_fst_245_, 2);
v_snd_246_ = lean_ctor_get(v_b_242_, 1);
lean_inc(v_snd_246_);
lean_dec_ref(v_b_242_);
lean_inc_ref(v_le_240_);
v___x_247_ = lean_apply_2(v_le_240_, v_fst_243_, v_fst_245_);
v___x_248_ = lean_unbox(v___x_247_);
if (v___x_248_ == 0)
{
uint8_t v___x_249_; 
lean_dec(v_snd_246_);
lean_dec(v_fst_245_);
lean_dec(v_snd_244_);
lean_dec(v_fst_243_);
lean_dec_ref(v_le_240_);
v___x_249_ = lean_unbox(v___x_247_);
return v___x_249_;
}
else
{
lean_object* v___x_250_; uint8_t v___x_251_; 
v___x_250_ = lean_apply_2(v_le_240_, v_fst_245_, v_fst_243_);
v___x_251_ = lean_unbox(v___x_250_);
if (v___x_251_ == 0)
{
uint8_t v___x_252_; 
lean_dec(v_snd_246_);
lean_dec(v_snd_244_);
v___x_252_ = lean_unbox(v___x_247_);
return v___x_252_;
}
else
{
uint8_t v___x_253_; 
v___x_253_ = lean_nat_dec_le(v_snd_244_, v_snd_246_);
lean_dec(v_snd_246_);
lean_dec(v_snd_244_);
return v___x_253_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_zipIdxLE___redArg___boxed(lean_object* v_le_254_, lean_object* v_a_255_, lean_object* v_b_256_){
_start:
{
uint8_t v_res_257_; lean_object* v_r_258_; 
v_res_257_ = l_List_zipIdxLE___redArg(v_le_254_, v_a_255_, v_b_256_);
v_r_258_ = lean_box(v_res_257_);
return v_r_258_;
}
}
LEAN_EXPORT uint8_t l_List_zipIdxLE(lean_object* v_00_u03b1_259_, lean_object* v_le_260_, lean_object* v_a_261_, lean_object* v_b_262_){
_start:
{
uint8_t v___x_263_; 
v___x_263_ = l_List_zipIdxLE___redArg(v_le_260_, v_a_261_, v_b_262_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_List_zipIdxLE___boxed(lean_object* v_00_u03b1_264_, lean_object* v_le_265_, lean_object* v_a_266_, lean_object* v_b_267_){
_start:
{
uint8_t v_res_268_; lean_object* v_r_269_; 
v_res_268_ = l_List_zipIdxLE(v_00_u03b1_264_, v_le_265_, v_a_266_, v_b_267_);
v_r_269_ = lean_box(v_res_268_);
return v_r_269_;
}
}
lean_object* runtime_initialize_Init_Ext(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Nat_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_List_Sort_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Nat_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_List_Sort_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_List_merge___auto__1 = _init_l_List_merge___auto__1();
lean_mark_persistent(l_List_merge___auto__1);
l_List_mergeSort___auto__1 = _init_l_List_mergeSort___auto__1();
lean_mark_persistent(l_List_mergeSort___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Ext(uint8_t builtin);
lean_object* initialize_Init_Data_List_Nat_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_List_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_List_Sort_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Nat_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Sort_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_List_Sort_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_List_Sort_Basic(builtin);
}
#ifdef __cplusplus
}
#endif

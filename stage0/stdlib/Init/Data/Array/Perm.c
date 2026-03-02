// Lean compiler output
// Module: Init.Data.Array.Perm
// Imports: import all Init.Data.Array.Basic public import Init.Data.Array.Basic import Init.Data.Array.Lemmas import Init.Data.List.Nat.Perm import Init.Data.List.Nat.TakeDrop import Init.Data.List.Perm import Init.Omega
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
static const lean_string_object l_Array_term___x7e___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Array"};
static const lean_object* l_Array_term___x7e___00__closed__0 = (const lean_object*)&l_Array_term___x7e___00__closed__0_value;
static const lean_string_object l_Array_term___x7e___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "term_~_"};
static const lean_object* l_Array_term___x7e___00__closed__1 = (const lean_object*)&l_Array_term___x7e___00__closed__1_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l_Array_term___x7e___00__closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_term___x7e___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_ctor_object l_Array_term___x7e___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_term___x7e___00__closed__2_value_aux_0),((lean_object*)&l_Array_term___x7e___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(188, 38, 75, 23, 236, 173, 138, 152)}};
static const lean_object* l_Array_term___x7e___00__closed__2 = (const lean_object*)&l_Array_term___x7e___00__closed__2_value;
static const lean_string_object l_Array_term___x7e___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Array_term___x7e___00__closed__3 = (const lean_object*)&l_Array_term___x7e___00__closed__3_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Array_term___x7e___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_term___x7e___00__closed__3_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Array_term___x7e___00__closed__4 = (const lean_object*)&l_Array_term___x7e___00__closed__4_value;
static const lean_string_object l_Array_term___x7e___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " ~ "};
static const lean_object* l_Array_term___x7e___00__closed__5 = (const lean_object*)&l_Array_term___x7e___00__closed__5_value;
static const lean_ctor_object l_Array_term___x7e___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Array_term___x7e___00__closed__5_value)}};
static const lean_object* l_Array_term___x7e___00__closed__6 = (const lean_object*)&l_Array_term___x7e___00__closed__6_value;
static const lean_string_object l_Array_term___x7e___00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Array_term___x7e___00__closed__7 = (const lean_object*)&l_Array_term___x7e___00__closed__7_value;
static const lean_ctor_object l_Array_term___x7e___00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_term___x7e___00__closed__7_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Array_term___x7e___00__closed__8 = (const lean_object*)&l_Array_term___x7e___00__closed__8_value;
static const lean_ctor_object l_Array_term___x7e___00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Array_term___x7e___00__closed__8_value),((lean_object*)(((size_t)(51) << 1) | 1))}};
static const lean_object* l_Array_term___x7e___00__closed__9 = (const lean_object*)&l_Array_term___x7e___00__closed__9_value;
static const lean_ctor_object l_Array_term___x7e___00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Array_term___x7e___00__closed__4_value),((lean_object*)&l_Array_term___x7e___00__closed__6_value),((lean_object*)&l_Array_term___x7e___00__closed__9_value)}};
static const lean_object* l_Array_term___x7e___00__closed__10 = (const lean_object*)&l_Array_term___x7e___00__closed__10_value;
static const lean_ctor_object l_Array_term___x7e___00__closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_Array_term___x7e___00__closed__2_value),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)&l_Array_term___x7e___00__closed__10_value)}};
static const lean_object* l_Array_term___x7e___00__closed__11 = (const lean_object*)&l_Array_term___x7e___00__closed__11_value;
LEAN_EXPORT const lean_object* l_Array_term___x7e__ = (const lean_object*)&l_Array_term___x7e___00__closed__11_value;
static const lean_string_object l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__0 = (const lean_object*)&l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__0_value;
static const lean_string_object l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__1 = (const lean_object*)&l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__1_value;
static const lean_string_object l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__2 = (const lean_object*)&l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__2_value;
static const lean_string_object l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__3 = (const lean_object*)&l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__3_value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__4_value_aux_0),((lean_object*)&l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__4_value_aux_1),((lean_object*)&l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__4_value_aux_2),((lean_object*)&l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__4 = (const lean_object*)&l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__4_value;
static const lean_string_object l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Perm"};
static const lean_object* l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__5 = (const lean_object*)&l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__5_value;
lean_object* l_String_toRawSubstring_x27(lean_object*);
static lean_once_cell_t l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__6;
static const lean_ctor_object l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(93, 39, 207, 243, 25, 131, 84, 93)}};
static const lean_object* l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__7 = (const lean_object*)&l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__7_value;
static const lean_ctor_object l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_term___x7e___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__8_value_aux_0),((lean_object*)&l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(255, 29, 113, 97, 69, 44, 10, 124)}};
static const lean_object* l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__8 = (const lean_object*)&l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__8_value;
static const lean_ctor_object l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__9 = (const lean_object*)&l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__9_value;
static const lean_ctor_object l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__8_value)}};
static const lean_object* l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__10 = (const lean_object*)&l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__10_value;
static const lean_string_object l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "List"};
static const lean_object* l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__11 = (const lean_object*)&l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__11_value;
static const lean_ctor_object l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__11_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__12_value_aux_0),((lean_object*)&l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(115, 187, 193, 253, 117, 51, 247, 91)}};
static const lean_object* l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__12 = (const lean_object*)&l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__12_value;
static const lean_ctor_object l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__12_value)}};
static const lean_object* l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__13 = (const lean_object*)&l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__13_value;
static const lean_ctor_object l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__13_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__14 = (const lean_object*)&l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__14_value;
static const lean_ctor_object l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__10_value),((lean_object*)&l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__14_value)}};
static const lean_object* l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__15 = (const lean_object*)&l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__15_value;
static const lean_ctor_object l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__9_value),((lean_object*)&l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__15_value)}};
static const lean_object* l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__16 = (const lean_object*)&l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__16_value;
static const lean_string_object l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__17 = (const lean_object*)&l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__17_value;
static const lean_ctor_object l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__17_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__18 = (const lean_object*)&l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__18_value;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array___aux__Init__Data__Array__Perm______unexpand__Array__Perm__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Array___aux__Init__Data__Array__Perm______unexpand__Array__Perm__1___closed__0 = (const lean_object*)&l_Array___aux__Init__Data__Array__Perm______unexpand__Array__Perm__1___closed__0_value;
static const lean_ctor_object l_Array___aux__Init__Data__Array__Perm______unexpand__Array__Perm__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array___aux__Init__Data__Array__Perm______unexpand__Array__Perm__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Array___aux__Init__Data__Array__Perm______unexpand__Array__Perm__1___closed__1 = (const lean_object*)&l_Array___aux__Init__Data__Array__Perm______unexpand__Array__Perm__1___closed__1_value;
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array___aux__Init__Data__Array__Perm______unexpand__Array__Perm__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array___aux__Init__Data__Array__Perm______unexpand__Array__Perm__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instTransPerm(lean_object*);
static lean_object* _init_l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__5));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = ((lean_object*)(l_Array_term___x7e___00__closed__2));
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 5);
lean_inc(x_10);
lean_dec_ref(x_2);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = lean_unsigned_to_nat(2u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
lean_dec(x_1);
x_15 = 0;
x_16 = l_Lean_SourceInfo_fromRef(x_10, x_15);
lean_dec(x_10);
x_17 = ((lean_object*)(l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__4));
x_18 = lean_obj_once(&l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__6, &l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__6_once, _init_l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__6);
x_19 = ((lean_object*)(l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__7));
x_20 = l_Lean_addMacroScope(x_8, x_19, x_9);
x_21 = ((lean_object*)(l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__16));
lean_inc(x_16);
x_22 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_22, 0, x_16);
lean_ctor_set(x_22, 1, x_18);
lean_ctor_set(x_22, 2, x_20);
lean_ctor_set(x_22, 3, x_21);
x_23 = ((lean_object*)(l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__18));
lean_inc(x_16);
x_24 = l_Lean_Syntax_node2(x_16, x_23, x_12, x_14);
x_25 = l_Lean_Syntax_node2(x_16, x_17, x_22, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_3);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Array___aux__Init__Data__Array__Perm______unexpand__Array__Perm__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = ((lean_object*)(l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__4));
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = ((lean_object*)(l_Array___aux__Init__Data__Array__Perm______unexpand__Array__Perm__1___closed__1));
lean_inc(x_9);
x_11 = l_Lean_Syntax_isOfKind(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
lean_dec(x_1);
x_16 = lean_unsigned_to_nat(2u);
lean_inc(x_15);
x_17 = l_Lean_Syntax_matchesNull(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_15);
lean_dec(x_9);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_3);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_20 = l_Lean_Syntax_getArg(x_15, x_8);
x_21 = l_Lean_Syntax_getArg(x_15, x_14);
lean_dec(x_15);
x_22 = l_Lean_replaceRef(x_9, x_2);
lean_dec(x_9);
x_23 = 0;
x_24 = l_Lean_SourceInfo_fromRef(x_22, x_23);
lean_dec(x_22);
x_25 = ((lean_object*)(l_Array_term___x7e___00__closed__2));
x_26 = ((lean_object*)(l_Array_term___x7e___00__closed__5));
lean_inc(x_24);
x_27 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_Syntax_node3(x_24, x_25, x_20, x_27, x_21);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_3);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array___aux__Init__Data__Array__Perm______unexpand__Array__Perm__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array___aux__Init__Data__Array__Perm______unexpand__Array__Perm__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_instTransPerm(lean_object* x_1) {
_start:
{
return lean_box(0);
}
}
lean_object* initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_List_Nat_Perm(uint8_t builtin);
lean_object* initialize_Init_Data_List_Nat_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_List_Perm(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Array_Perm(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Nat_Perm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Nat_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Perm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

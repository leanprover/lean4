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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_term___x7e___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Array"};
static const lean_object* l_Array_term___x7e___00__closed__0 = (const lean_object*)&l_Array_term___x7e___00__closed__0_value;
static const lean_string_object l_Array_term___x7e___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "term_~_"};
static const lean_object* l_Array_term___x7e___00__closed__1 = (const lean_object*)&l_Array_term___x7e___00__closed__1_value;
static const lean_ctor_object l_Array_term___x7e___00__closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_term___x7e___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_ctor_object l_Array_term___x7e___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_term___x7e___00__closed__2_value_aux_0),((lean_object*)&l_Array_term___x7e___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(188, 38, 75, 23, 236, 173, 138, 152)}};
static const lean_object* l_Array_term___x7e___00__closed__2 = (const lean_object*)&l_Array_term___x7e___00__closed__2_value;
static const lean_string_object l_Array_term___x7e___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Array_term___x7e___00__closed__3 = (const lean_object*)&l_Array_term___x7e___00__closed__3_value;
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
static const lean_ctor_object l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__4_value_aux_0),((lean_object*)&l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__4_value_aux_1),((lean_object*)&l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__4_value_aux_2),((lean_object*)&l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__4 = (const lean_object*)&l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__4_value;
static const lean_string_object l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Perm"};
static const lean_object* l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__5 = (const lean_object*)&l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__5_value;
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
LEAN_EXPORT lean_object* l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array___aux__Init__Data__Array__Perm______unexpand__Array__Perm__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Array___aux__Init__Data__Array__Perm______unexpand__Array__Perm__1___closed__0 = (const lean_object*)&l_Array___aux__Init__Data__Array__Perm______unexpand__Array__Perm__1___closed__0_value;
static const lean_ctor_object l_Array___aux__Init__Data__Array__Perm______unexpand__Array__Perm__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array___aux__Init__Data__Array__Perm______unexpand__Array__Perm__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Array___aux__Init__Data__Array__Perm______unexpand__Array__Perm__1___closed__1 = (const lean_object*)&l_Array___aux__Init__Data__Array__Perm______unexpand__Array__Perm__1___closed__1_value;
LEAN_EXPORT lean_object* l_Array___aux__Init__Data__Array__Perm______unexpand__Array__Perm__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array___aux__Init__Data__Array__Perm______unexpand__Array__Perm__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instTransPerm(lean_object*);
static lean_object* _init_l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__6(void){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_37_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__5));
v___x_38_ = l_String_toRawSubstring_x27(v___x_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1(lean_object* v_x_67_, lean_object* v_a_68_, lean_object* v_a_69_){
_start:
{
lean_object* v___x_70_; uint8_t v___x_71_; 
v___x_70_ = ((lean_object*)(l_Array_term___x7e___00__closed__2));
lean_inc(v_x_67_);
v___x_71_ = l_Lean_Syntax_isOfKind(v_x_67_, v___x_70_);
if (v___x_71_ == 0)
{
lean_object* v___x_72_; lean_object* v___x_73_; 
lean_dec_ref(v_a_68_);
lean_dec(v_x_67_);
v___x_72_ = lean_box(1);
v___x_73_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_73_, 0, v___x_72_);
lean_ctor_set(v___x_73_, 1, v_a_69_);
return v___x_73_;
}
else
{
lean_object* v_quotContext_74_; lean_object* v_currMacroScope_75_; lean_object* v_ref_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; uint8_t v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v_quotContext_74_ = lean_ctor_get(v_a_68_, 1);
lean_inc(v_quotContext_74_);
v_currMacroScope_75_ = lean_ctor_get(v_a_68_, 2);
lean_inc(v_currMacroScope_75_);
v_ref_76_ = lean_ctor_get(v_a_68_, 5);
lean_inc(v_ref_76_);
lean_dec_ref(v_a_68_);
v___x_77_ = lean_unsigned_to_nat(0u);
v___x_78_ = l_Lean_Syntax_getArg(v_x_67_, v___x_77_);
v___x_79_ = lean_unsigned_to_nat(2u);
v___x_80_ = l_Lean_Syntax_getArg(v_x_67_, v___x_79_);
lean_dec(v_x_67_);
v___x_81_ = 0;
v___x_82_ = l_Lean_SourceInfo_fromRef(v_ref_76_, v___x_81_);
lean_dec(v_ref_76_);
v___x_83_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__4));
v___x_84_ = lean_obj_once(&l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__6, &l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__6_once, _init_l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__6);
v___x_85_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__7));
v___x_86_ = l_Lean_addMacroScope(v_quotContext_74_, v___x_85_, v_currMacroScope_75_);
v___x_87_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__16));
lean_inc(v___x_82_);
v___x_88_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_88_, 0, v___x_82_);
lean_ctor_set(v___x_88_, 1, v___x_84_);
lean_ctor_set(v___x_88_, 2, v___x_86_);
lean_ctor_set(v___x_88_, 3, v___x_87_);
v___x_89_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__18));
lean_inc(v___x_82_);
v___x_90_ = l_Lean_Syntax_node2(v___x_82_, v___x_89_, v___x_78_, v___x_80_);
v___x_91_ = l_Lean_Syntax_node2(v___x_82_, v___x_83_, v___x_88_, v___x_90_);
v___x_92_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_92_, 0, v___x_91_);
lean_ctor_set(v___x_92_, 1, v_a_69_);
return v___x_92_;
}
}
}
LEAN_EXPORT lean_object* l_Array___aux__Init__Data__Array__Perm______unexpand__Array__Perm__1(lean_object* v_x_96_, lean_object* v_a_97_, lean_object* v_a_98_){
_start:
{
lean_object* v___x_99_; uint8_t v___x_100_; 
v___x_99_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__4));
lean_inc(v_x_96_);
v___x_100_ = l_Lean_Syntax_isOfKind(v_x_96_, v___x_99_);
if (v___x_100_ == 0)
{
lean_object* v___x_101_; lean_object* v___x_102_; 
lean_dec(v_x_96_);
v___x_101_ = lean_box(0);
v___x_102_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_102_, 0, v___x_101_);
lean_ctor_set(v___x_102_, 1, v_a_98_);
return v___x_102_;
}
else
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; uint8_t v___x_106_; 
v___x_103_ = lean_unsigned_to_nat(0u);
v___x_104_ = l_Lean_Syntax_getArg(v_x_96_, v___x_103_);
v___x_105_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Perm______unexpand__Array__Perm__1___closed__1));
lean_inc(v___x_104_);
v___x_106_ = l_Lean_Syntax_isOfKind(v___x_104_, v___x_105_);
if (v___x_106_ == 0)
{
lean_object* v___x_107_; lean_object* v___x_108_; 
lean_dec(v___x_104_);
lean_dec(v_x_96_);
v___x_107_ = lean_box(0);
v___x_108_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_108_, 0, v___x_107_);
lean_ctor_set(v___x_108_, 1, v_a_98_);
return v___x_108_;
}
else
{
lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; uint8_t v___x_112_; 
v___x_109_ = lean_unsigned_to_nat(1u);
v___x_110_ = l_Lean_Syntax_getArg(v_x_96_, v___x_109_);
lean_dec(v_x_96_);
v___x_111_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_110_);
v___x_112_ = l_Lean_Syntax_matchesNull(v___x_110_, v___x_111_);
if (v___x_112_ == 0)
{
lean_object* v___x_113_; lean_object* v___x_114_; 
lean_dec(v___x_110_);
lean_dec(v___x_104_);
v___x_113_ = lean_box(0);
v___x_114_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_114_, 0, v___x_113_);
lean_ctor_set(v___x_114_, 1, v_a_98_);
return v___x_114_;
}
else
{
lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v_ref_117_; uint8_t v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_115_ = l_Lean_Syntax_getArg(v___x_110_, v___x_103_);
v___x_116_ = l_Lean_Syntax_getArg(v___x_110_, v___x_109_);
lean_dec(v___x_110_);
v_ref_117_ = l_Lean_replaceRef(v___x_104_, v_a_97_);
lean_dec(v___x_104_);
v___x_118_ = 0;
v___x_119_ = l_Lean_SourceInfo_fromRef(v_ref_117_, v___x_118_);
lean_dec(v_ref_117_);
v___x_120_ = ((lean_object*)(l_Array_term___x7e___00__closed__2));
v___x_121_ = ((lean_object*)(l_Array_term___x7e___00__closed__5));
lean_inc(v___x_119_);
v___x_122_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_122_, 0, v___x_119_);
lean_ctor_set(v___x_122_, 1, v___x_121_);
v___x_123_ = l_Lean_Syntax_node3(v___x_119_, v___x_120_, v___x_115_, v___x_122_, v___x_116_);
v___x_124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_124_, 0, v___x_123_);
lean_ctor_set(v___x_124_, 1, v_a_98_);
return v___x_124_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array___aux__Init__Data__Array__Perm______unexpand__Array__Perm__1___boxed(lean_object* v_x_125_, lean_object* v_a_126_, lean_object* v_a_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l_Array___aux__Init__Data__Array__Perm______unexpand__Array__Perm__1(v_x_125_, v_a_126_, v_a_127_);
lean_dec(v_a_126_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l_Array_instTransPerm(lean_object* v_00_u03b1_129_){
_start:
{
lean_object* v___x_130_; 
v___x_130_ = lean_box(0);
return v___x_130_;
}
}
lean_object* runtime_initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Nat_Perm(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Nat_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Perm(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Array_Perm(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Nat_Perm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Nat_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Perm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Array_Perm(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
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
res = runtime_initialize_Init_Data_Array_Perm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Array_Perm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Array_Perm(builtin);
}
#ifdef __cplusplus
}
#endif

// Lean compiler output
// Module: Init.Data.Vector.Perm
// Imports: import all Init.Data.Array.Basic public import Init.Data.Array.Perm import all Init.Data.Vector.Basic public import Init.Data.Vector.Basic import Init.Data.List.Nat.Perm import Init.Data.Vector.Lemmas
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
static const lean_string_object l_Vector_term___x7e___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Vector"};
static const lean_object* l_Vector_term___x7e___00__closed__0 = (const lean_object*)&l_Vector_term___x7e___00__closed__0_value;
static const lean_string_object l_Vector_term___x7e___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "term_~_"};
static const lean_object* l_Vector_term___x7e___00__closed__1 = (const lean_object*)&l_Vector_term___x7e___00__closed__1_value;
static const lean_ctor_object l_Vector_term___x7e___00__closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Vector_term___x7e___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(209, 122, 98, 30, 71, 224, 237, 30)}};
static const lean_ctor_object l_Vector_term___x7e___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector_term___x7e___00__closed__2_value_aux_0),((lean_object*)&l_Vector_term___x7e___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(60, 120, 18, 31, 3, 64, 187, 80)}};
static const lean_object* l_Vector_term___x7e___00__closed__2 = (const lean_object*)&l_Vector_term___x7e___00__closed__2_value;
static const lean_string_object l_Vector_term___x7e___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Vector_term___x7e___00__closed__3 = (const lean_object*)&l_Vector_term___x7e___00__closed__3_value;
static const lean_ctor_object l_Vector_term___x7e___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Vector_term___x7e___00__closed__3_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Vector_term___x7e___00__closed__4 = (const lean_object*)&l_Vector_term___x7e___00__closed__4_value;
static const lean_string_object l_Vector_term___x7e___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " ~ "};
static const lean_object* l_Vector_term___x7e___00__closed__5 = (const lean_object*)&l_Vector_term___x7e___00__closed__5_value;
static const lean_ctor_object l_Vector_term___x7e___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Vector_term___x7e___00__closed__5_value)}};
static const lean_object* l_Vector_term___x7e___00__closed__6 = (const lean_object*)&l_Vector_term___x7e___00__closed__6_value;
static const lean_string_object l_Vector_term___x7e___00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Vector_term___x7e___00__closed__7 = (const lean_object*)&l_Vector_term___x7e___00__closed__7_value;
static const lean_ctor_object l_Vector_term___x7e___00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Vector_term___x7e___00__closed__7_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Vector_term___x7e___00__closed__8 = (const lean_object*)&l_Vector_term___x7e___00__closed__8_value;
static const lean_ctor_object l_Vector_term___x7e___00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Vector_term___x7e___00__closed__8_value),((lean_object*)(((size_t)(51) << 1) | 1))}};
static const lean_object* l_Vector_term___x7e___00__closed__9 = (const lean_object*)&l_Vector_term___x7e___00__closed__9_value;
static const lean_ctor_object l_Vector_term___x7e___00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Vector_term___x7e___00__closed__4_value),((lean_object*)&l_Vector_term___x7e___00__closed__6_value),((lean_object*)&l_Vector_term___x7e___00__closed__9_value)}};
static const lean_object* l_Vector_term___x7e___00__closed__10 = (const lean_object*)&l_Vector_term___x7e___00__closed__10_value;
static const lean_ctor_object l_Vector_term___x7e___00__closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_Vector_term___x7e___00__closed__2_value),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)&l_Vector_term___x7e___00__closed__10_value)}};
static const lean_object* l_Vector_term___x7e___00__closed__11 = (const lean_object*)&l_Vector_term___x7e___00__closed__11_value;
LEAN_EXPORT const lean_object* l_Vector_term___x7e__ = (const lean_object*)&l_Vector_term___x7e___00__closed__11_value;
static const lean_string_object l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__0 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__0_value;
static const lean_string_object l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__1 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__1_value;
static const lean_string_object l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__2 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__2_value;
static const lean_string_object l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__3 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__3_value;
static const lean_ctor_object l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__4_value_aux_0),((lean_object*)&l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__4_value_aux_1),((lean_object*)&l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__4_value_aux_2),((lean_object*)&l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__4 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__4_value;
static const lean_string_object l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Perm"};
static const lean_object* l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__5 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__5_value;
static lean_once_cell_t l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__6;
static const lean_ctor_object l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(93, 39, 207, 243, 25, 131, 84, 93)}};
static const lean_object* l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__7 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__7_value;
static const lean_ctor_object l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Vector_term___x7e___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(209, 122, 98, 30, 71, 224, 237, 30)}};
static const lean_ctor_object l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__8_value_aux_0),((lean_object*)&l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(127, 36, 73, 37, 2, 50, 147, 116)}};
static const lean_object* l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__8 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__8_value;
static const lean_ctor_object l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__9 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__9_value;
static const lean_ctor_object l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__8_value)}};
static const lean_object* l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__10 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__10_value;
static const lean_string_object l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Array"};
static const lean_object* l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__11 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__11_value;
static const lean_ctor_object l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__11_value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_ctor_object l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__12_value_aux_0),((lean_object*)&l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(255, 29, 113, 97, 69, 44, 10, 124)}};
static const lean_object* l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__12 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__12_value;
static const lean_ctor_object l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__12_value)}};
static const lean_object* l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__13 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__13_value;
static const lean_string_object l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "List"};
static const lean_object* l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__14 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__14_value;
static const lean_ctor_object l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__15_value_aux_0),((lean_object*)&l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(115, 187, 193, 253, 117, 51, 247, 91)}};
static const lean_object* l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__15 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__15_value;
static const lean_ctor_object l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__15_value)}};
static const lean_object* l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__16 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__16_value;
static const lean_ctor_object l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__16_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__17 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__17_value;
static const lean_ctor_object l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__13_value),((lean_object*)&l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__17_value)}};
static const lean_object* l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__18 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__18_value;
static const lean_ctor_object l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__10_value),((lean_object*)&l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__18_value)}};
static const lean_object* l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__19 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__19_value;
static const lean_ctor_object l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__9_value),((lean_object*)&l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__19_value)}};
static const lean_object* l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__20 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__20_value;
static const lean_string_object l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__21 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__21_value;
static const lean_ctor_object l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__22 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__22_value;
LEAN_EXPORT lean_object* l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Vector___aux__Init__Data__Vector__Perm______unexpand__Vector__Perm__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Vector___aux__Init__Data__Vector__Perm______unexpand__Vector__Perm__1___closed__0 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Perm______unexpand__Vector__Perm__1___closed__0_value;
static const lean_ctor_object l_Vector___aux__Init__Data__Vector__Perm______unexpand__Vector__Perm__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Vector___aux__Init__Data__Vector__Perm______unexpand__Vector__Perm__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Vector___aux__Init__Data__Vector__Perm______unexpand__Vector__Perm__1___closed__1 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Perm______unexpand__Vector__Perm__1___closed__1_value;
LEAN_EXPORT lean_object* l_Vector___aux__Init__Data__Vector__Perm______unexpand__Vector__Perm__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector___aux__Init__Data__Vector__Perm______unexpand__Vector__Perm__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instTransPerm(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instTransPerm___boxed(lean_object*, lean_object*);
static lean_object* _init_l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__6(void){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_37_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__5));
v___x_38_ = l_String_toRawSubstring_x27(v___x_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1(lean_object* v_x_76_, lean_object* v_a_77_, lean_object* v_a_78_){
_start:
{
lean_object* v___x_79_; uint8_t v___x_80_; 
v___x_79_ = ((lean_object*)(l_Vector_term___x7e___00__closed__2));
lean_inc(v_x_76_);
v___x_80_ = l_Lean_Syntax_isOfKind(v_x_76_, v___x_79_);
if (v___x_80_ == 0)
{
lean_object* v___x_81_; lean_object* v___x_82_; 
lean_dec(v_x_76_);
v___x_81_ = lean_box(1);
v___x_82_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_82_, 0, v___x_81_);
lean_ctor_set(v___x_82_, 1, v_a_78_);
return v___x_82_;
}
else
{
lean_object* v_quotContext_83_; lean_object* v_currMacroScope_84_; lean_object* v_ref_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; uint8_t v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v_quotContext_83_ = lean_ctor_get(v_a_77_, 1);
v_currMacroScope_84_ = lean_ctor_get(v_a_77_, 2);
v_ref_85_ = lean_ctor_get(v_a_77_, 5);
v___x_86_ = lean_unsigned_to_nat(0u);
v___x_87_ = l_Lean_Syntax_getArg(v_x_76_, v___x_86_);
v___x_88_ = lean_unsigned_to_nat(2u);
v___x_89_ = l_Lean_Syntax_getArg(v_x_76_, v___x_88_);
lean_dec(v_x_76_);
v___x_90_ = 0;
v___x_91_ = l_Lean_SourceInfo_fromRef(v_ref_85_, v___x_90_);
v___x_92_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__4));
v___x_93_ = lean_obj_once(&l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__6, &l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__6_once, _init_l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__6);
v___x_94_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__7));
lean_inc(v_currMacroScope_84_);
lean_inc(v_quotContext_83_);
v___x_95_ = l_Lean_addMacroScope(v_quotContext_83_, v___x_94_, v_currMacroScope_84_);
v___x_96_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__20));
lean_inc_n(v___x_91_, 2);
v___x_97_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_97_, 0, v___x_91_);
lean_ctor_set(v___x_97_, 1, v___x_93_);
lean_ctor_set(v___x_97_, 2, v___x_95_);
lean_ctor_set(v___x_97_, 3, v___x_96_);
v___x_98_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__22));
v___x_99_ = l_Lean_Syntax_node2(v___x_91_, v___x_98_, v___x_87_, v___x_89_);
v___x_100_ = l_Lean_Syntax_node2(v___x_91_, v___x_92_, v___x_97_, v___x_99_);
v___x_101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
lean_ctor_set(v___x_101_, 1, v_a_78_);
return v___x_101_;
}
}
}
LEAN_EXPORT lean_object* l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___boxed(lean_object* v_x_102_, lean_object* v_a_103_, lean_object* v_a_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1(v_x_102_, v_a_103_, v_a_104_);
lean_dec_ref(v_a_103_);
return v_res_105_;
}
}
LEAN_EXPORT lean_object* l_Vector___aux__Init__Data__Vector__Perm______unexpand__Vector__Perm__1(lean_object* v_x_109_, lean_object* v_a_110_, lean_object* v_a_111_){
_start:
{
lean_object* v___x_112_; uint8_t v___x_113_; 
v___x_112_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__4));
lean_inc(v_x_109_);
v___x_113_ = l_Lean_Syntax_isOfKind(v_x_109_, v___x_112_);
if (v___x_113_ == 0)
{
lean_object* v___x_114_; lean_object* v___x_115_; 
lean_dec(v_x_109_);
v___x_114_ = lean_box(0);
v___x_115_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_115_, 0, v___x_114_);
lean_ctor_set(v___x_115_, 1, v_a_111_);
return v___x_115_;
}
else
{
lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; uint8_t v___x_119_; 
v___x_116_ = lean_unsigned_to_nat(0u);
v___x_117_ = l_Lean_Syntax_getArg(v_x_109_, v___x_116_);
v___x_118_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Perm______unexpand__Vector__Perm__1___closed__1));
lean_inc(v___x_117_);
v___x_119_ = l_Lean_Syntax_isOfKind(v___x_117_, v___x_118_);
if (v___x_119_ == 0)
{
lean_object* v___x_120_; lean_object* v___x_121_; 
lean_dec(v___x_117_);
lean_dec(v_x_109_);
v___x_120_ = lean_box(0);
v___x_121_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_121_, 0, v___x_120_);
lean_ctor_set(v___x_121_, 1, v_a_111_);
return v___x_121_;
}
else
{
lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; uint8_t v___x_125_; 
v___x_122_ = lean_unsigned_to_nat(1u);
v___x_123_ = l_Lean_Syntax_getArg(v_x_109_, v___x_122_);
lean_dec(v_x_109_);
v___x_124_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_123_);
v___x_125_ = l_Lean_Syntax_matchesNull(v___x_123_, v___x_124_);
if (v___x_125_ == 0)
{
lean_object* v___x_126_; lean_object* v___x_127_; 
lean_dec(v___x_123_);
lean_dec(v___x_117_);
v___x_126_ = lean_box(0);
v___x_127_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_127_, 0, v___x_126_);
lean_ctor_set(v___x_127_, 1, v_a_111_);
return v___x_127_;
}
else
{
lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v_ref_130_; uint8_t v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_128_ = l_Lean_Syntax_getArg(v___x_123_, v___x_116_);
v___x_129_ = l_Lean_Syntax_getArg(v___x_123_, v___x_122_);
lean_dec(v___x_123_);
v_ref_130_ = l_Lean_replaceRef(v___x_117_, v_a_110_);
lean_dec(v___x_117_);
v___x_131_ = 0;
v___x_132_ = l_Lean_SourceInfo_fromRef(v_ref_130_, v___x_131_);
lean_dec(v_ref_130_);
v___x_133_ = ((lean_object*)(l_Vector_term___x7e___00__closed__2));
v___x_134_ = ((lean_object*)(l_Vector_term___x7e___00__closed__5));
lean_inc(v___x_132_);
v___x_135_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_135_, 0, v___x_132_);
lean_ctor_set(v___x_135_, 1, v___x_134_);
v___x_136_ = l_Lean_Syntax_node3(v___x_132_, v___x_133_, v___x_128_, v___x_135_, v___x_129_);
v___x_137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_137_, 0, v___x_136_);
lean_ctor_set(v___x_137_, 1, v_a_111_);
return v___x_137_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Vector___aux__Init__Data__Vector__Perm______unexpand__Vector__Perm__1___boxed(lean_object* v_x_138_, lean_object* v_a_139_, lean_object* v_a_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_Vector___aux__Init__Data__Vector__Perm______unexpand__Vector__Perm__1(v_x_138_, v_a_139_, v_a_140_);
lean_dec(v_a_139_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_Vector_instTransPerm(lean_object* v_00_u03b1_142_, lean_object* v_n_143_){
_start:
{
lean_object* v___x_144_; 
v___x_144_ = lean_box(0);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_Vector_instTransPerm___boxed(lean_object* v_00_u03b1_145_, lean_object* v_n_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l_Vector_instTransPerm(v_00_u03b1_145_, v_n_146_);
lean_dec(v_n_146_);
return v_res_147_;
}
}
lean_object* runtime_initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Perm(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Vector_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Vector_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Nat_Perm(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Vector_Lemmas(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Vector_Perm(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Perm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Vector_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Vector_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Nat_Perm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Vector_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Vector_Perm(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Perm(uint8_t builtin);
lean_object* initialize_Init_Data_Vector_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Vector_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_List_Nat_Perm(uint8_t builtin);
lean_object* initialize_Init_Data_Vector_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Vector_Perm(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Perm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Vector_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Vector_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Nat_Perm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Vector_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Vector_Perm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Vector_Perm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Vector_Perm(builtin);
}
#ifdef __cplusplus
}
#endif

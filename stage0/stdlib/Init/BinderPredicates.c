// Lean compiler output
// Module: Init.BinderPredicates
// Imports: public meta import Init.Grind.Tactics public import Init.Notation import Init.Meta.Defs import Init.NotationExtra
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
extern lean_object* l_Lean_binderIdent;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_binderPred_quot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_binderPred_quot___closed__0 = (const lean_object*)&l_Lean_binderPred_quot___closed__0_value;
static const lean_string_object l_Lean_binderPred_quot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_binderPred_quot___closed__1 = (const lean_object*)&l_Lean_binderPred_quot___closed__1_value;
static const lean_string_object l_Lean_binderPred_quot___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_binderPred_quot___closed__2 = (const lean_object*)&l_Lean_binderPred_quot___closed__2_value;
static const lean_string_object l_Lean_binderPred_quot___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "quot"};
static const lean_object* l_Lean_binderPred_quot___closed__3 = (const lean_object*)&l_Lean_binderPred_quot___closed__3_value;
static const lean_ctor_object l_Lean_binderPred_quot___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_binderPred_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_binderPred_quot___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_binderPred_quot___closed__4_value_aux_0),((lean_object*)&l_Lean_binderPred_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_binderPred_quot___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_binderPred_quot___closed__4_value_aux_1),((lean_object*)&l_Lean_binderPred_quot___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_binderPred_quot___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_binderPred_quot___closed__4_value_aux_2),((lean_object*)&l_Lean_binderPred_quot___closed__3_value),LEAN_SCALAR_PTR_LITERAL(145, 163, 173, 41, 168, 168, 65, 81)}};
static const lean_object* l_Lean_binderPred_quot___closed__4 = (const lean_object*)&l_Lean_binderPred_quot___closed__4_value;
static const lean_string_object l_Lean_binderPred_quot___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "binderPred"};
static const lean_object* l_Lean_binderPred_quot___closed__5 = (const lean_object*)&l_Lean_binderPred_quot___closed__5_value;
static const lean_ctor_object l_Lean_binderPred_quot___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_binderPred_quot___closed__5_value),LEAN_SCALAR_PTR_LITERAL(218, 134, 142, 164, 134, 201, 62, 191)}};
static const lean_ctor_object l_Lean_binderPred_quot___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_binderPred_quot___closed__6_value_aux_0),((lean_object*)&l_Lean_binderPred_quot___closed__3_value),LEAN_SCALAR_PTR_LITERAL(204, 41, 202, 236, 139, 197, 16, 246)}};
static const lean_object* l_Lean_binderPred_quot___closed__6 = (const lean_object*)&l_Lean_binderPred_quot___closed__6_value;
static const lean_string_object l_Lean_binderPred_quot___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Lean_binderPred_quot___closed__7 = (const lean_object*)&l_Lean_binderPred_quot___closed__7_value;
static const lean_ctor_object l_Lean_binderPred_quot___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_binderPred_quot___closed__7_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Lean_binderPred_quot___closed__8 = (const lean_object*)&l_Lean_binderPred_quot___closed__8_value;
static const lean_string_object l_Lean_binderPred_quot___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "`(binderPred| "};
static const lean_object* l_Lean_binderPred_quot___closed__9 = (const lean_object*)&l_Lean_binderPred_quot___closed__9_value;
static const lean_ctor_object l_Lean_binderPred_quot___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_binderPred_quot___closed__9_value)}};
static const lean_object* l_Lean_binderPred_quot___closed__10 = (const lean_object*)&l_Lean_binderPred_quot___closed__10_value;
static const lean_ctor_object l_Lean_binderPred_quot___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_binderPred_quot___closed__5_value),LEAN_SCALAR_PTR_LITERAL(218, 134, 142, 164, 134, 201, 62, 191)}};
static const lean_object* l_Lean_binderPred_quot___closed__11 = (const lean_object*)&l_Lean_binderPred_quot___closed__11_value;
static const lean_ctor_object l_Lean_binderPred_quot___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_binderPred_quot___closed__11_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_binderPred_quot___closed__12 = (const lean_object*)&l_Lean_binderPred_quot___closed__12_value;
static const lean_string_object l_Lean_binderPred_quot___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_binderPred_quot___closed__13 = (const lean_object*)&l_Lean_binderPred_quot___closed__13_value;
static const lean_ctor_object l_Lean_binderPred_quot___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_binderPred_quot___closed__13_value)}};
static const lean_object* l_Lean_binderPred_quot___closed__14 = (const lean_object*)&l_Lean_binderPred_quot___closed__14_value;
static const lean_ctor_object l_Lean_binderPred_quot___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_binderPred_quot___closed__8_value),((lean_object*)&l_Lean_binderPred_quot___closed__12_value),((lean_object*)&l_Lean_binderPred_quot___closed__14_value)}};
static const lean_object* l_Lean_binderPred_quot___closed__15 = (const lean_object*)&l_Lean_binderPred_quot___closed__15_value;
static const lean_ctor_object l_Lean_binderPred_quot___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_binderPred_quot___closed__8_value),((lean_object*)&l_Lean_binderPred_quot___closed__10_value),((lean_object*)&l_Lean_binderPred_quot___closed__15_value)}};
static const lean_object* l_Lean_binderPred_quot___closed__16 = (const lean_object*)&l_Lean_binderPred_quot___closed__16_value;
static const lean_ctor_object l_Lean_binderPred_quot___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_binderPred_quot___closed__6_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_binderPred_quot___closed__16_value)}};
static const lean_object* l_Lean_binderPred_quot___closed__17 = (const lean_object*)&l_Lean_binderPred_quot___closed__17_value;
static const lean_ctor_object l_Lean_binderPred_quot___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_binderPred_quot___closed__4_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_binderPred_quot___closed__17_value)}};
static const lean_object* l_Lean_binderPred_quot___closed__18 = (const lean_object*)&l_Lean_binderPred_quot___closed__18_value;
LEAN_EXPORT const lean_object* l_Lean_binderPred_quot = (const lean_object*)&l_Lean_binderPred_quot___closed__18_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Category_binderPred;
static const lean_string_object l_Lean_termSatisfies__binder__pred_x25_____00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "termSatisfies_binder_pred%__"};
static const lean_object* l_Lean_termSatisfies__binder__pred_x25_____00__closed__0 = (const lean_object*)&l_Lean_termSatisfies__binder__pred_x25_____00__closed__0_value;
static const lean_ctor_object l_Lean_termSatisfies__binder__pred_x25_____00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_binderPred_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_termSatisfies__binder__pred_x25_____00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_termSatisfies__binder__pred_x25_____00__closed__1_value_aux_0),((lean_object*)&l_Lean_termSatisfies__binder__pred_x25_____00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(35, 32, 166, 185, 227, 132, 228, 81)}};
static const lean_object* l_Lean_termSatisfies__binder__pred_x25_____00__closed__1 = (const lean_object*)&l_Lean_termSatisfies__binder__pred_x25_____00__closed__1_value;
static const lean_string_object l_Lean_termSatisfies__binder__pred_x25_____00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "satisfies_binder_pred% "};
static const lean_object* l_Lean_termSatisfies__binder__pred_x25_____00__closed__2 = (const lean_object*)&l_Lean_termSatisfies__binder__pred_x25_____00__closed__2_value;
static const lean_ctor_object l_Lean_termSatisfies__binder__pred_x25_____00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_termSatisfies__binder__pred_x25_____00__closed__2_value)}};
static const lean_object* l_Lean_termSatisfies__binder__pred_x25_____00__closed__3 = (const lean_object*)&l_Lean_termSatisfies__binder__pred_x25_____00__closed__3_value;
static const lean_string_object l_Lean_termSatisfies__binder__pred_x25_____00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Lean_termSatisfies__binder__pred_x25_____00__closed__4 = (const lean_object*)&l_Lean_termSatisfies__binder__pred_x25_____00__closed__4_value;
static const lean_ctor_object l_Lean_termSatisfies__binder__pred_x25_____00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_termSatisfies__binder__pred_x25_____00__closed__4_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Lean_termSatisfies__binder__pred_x25_____00__closed__5 = (const lean_object*)&l_Lean_termSatisfies__binder__pred_x25_____00__closed__5_value;
static const lean_ctor_object l_Lean_termSatisfies__binder__pred_x25_____00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_termSatisfies__binder__pred_x25_____00__closed__5_value),((lean_object*)(((size_t)(1024) << 1) | 1))}};
static const lean_object* l_Lean_termSatisfies__binder__pred_x25_____00__closed__6 = (const lean_object*)&l_Lean_termSatisfies__binder__pred_x25_____00__closed__6_value;
static const lean_ctor_object l_Lean_termSatisfies__binder__pred_x25_____00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_binderPred_quot___closed__8_value),((lean_object*)&l_Lean_termSatisfies__binder__pred_x25_____00__closed__3_value),((lean_object*)&l_Lean_termSatisfies__binder__pred_x25_____00__closed__6_value)}};
static const lean_object* l_Lean_termSatisfies__binder__pred_x25_____00__closed__7 = (const lean_object*)&l_Lean_termSatisfies__binder__pred_x25_____00__closed__7_value;
static const lean_ctor_object l_Lean_termSatisfies__binder__pred_x25_____00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_binderPred_quot___closed__8_value),((lean_object*)&l_Lean_termSatisfies__binder__pred_x25_____00__closed__7_value),((lean_object*)&l_Lean_binderPred_quot___closed__12_value)}};
static const lean_object* l_Lean_termSatisfies__binder__pred_x25_____00__closed__8 = (const lean_object*)&l_Lean_termSatisfies__binder__pred_x25_____00__closed__8_value;
static const lean_ctor_object l_Lean_termSatisfies__binder__pred_x25_____00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_termSatisfies__binder__pred_x25_____00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_termSatisfies__binder__pred_x25_____00__closed__8_value)}};
static const lean_object* l_Lean_termSatisfies__binder__pred_x25_____00__closed__9 = (const lean_object*)&l_Lean_termSatisfies__binder__pred_x25_____00__closed__9_value;
LEAN_EXPORT const lean_object* l_Lean_termSatisfies__binder__pred_x25____ = (const lean_object*)&l_Lean_termSatisfies__binder__pred_x25_____00__closed__9_value;
static const lean_string_object l_Lean_term_u2203_____x2c___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 9, .m_data = "term∃__,_"};
static const lean_object* l_Lean_term_u2203_____x2c___00__closed__0 = (const lean_object*)&l_Lean_term_u2203_____x2c___00__closed__0_value;
static const lean_ctor_object l_Lean_term_u2203_____x2c___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_binderPred_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_term_u2203_____x2c___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_term_u2203_____x2c___00__closed__1_value_aux_0),((lean_object*)&l_Lean_term_u2203_____x2c___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(25, 165, 221, 98, 134, 231, 221, 237)}};
static const lean_object* l_Lean_term_u2203_____x2c___00__closed__1 = (const lean_object*)&l_Lean_term_u2203_____x2c___00__closed__1_value;
static const lean_string_object l_Lean_term_u2203_____x2c___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 2, .m_data = "∃ "};
static const lean_object* l_Lean_term_u2203_____x2c___00__closed__2 = (const lean_object*)&l_Lean_term_u2203_____x2c___00__closed__2_value;
static const lean_ctor_object l_Lean_term_u2203_____x2c___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_term_u2203_____x2c___00__closed__2_value)}};
static const lean_object* l_Lean_term_u2203_____x2c___00__closed__3 = (const lean_object*)&l_Lean_term_u2203_____x2c___00__closed__3_value;
static lean_once_cell_t l_Lean_term_u2203_____x2c___00__closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_term_u2203_____x2c___00__closed__4;
static lean_once_cell_t l_Lean_term_u2203_____x2c___00__closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_term_u2203_____x2c___00__closed__5;
static const lean_string_object l_Lean_term_u2203_____x2c___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_Lean_term_u2203_____x2c___00__closed__6 = (const lean_object*)&l_Lean_term_u2203_____x2c___00__closed__6_value;
static const lean_ctor_object l_Lean_term_u2203_____x2c___00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_term_u2203_____x2c___00__closed__6_value)}};
static const lean_object* l_Lean_term_u2203_____x2c___00__closed__7 = (const lean_object*)&l_Lean_term_u2203_____x2c___00__closed__7_value;
static lean_once_cell_t l_Lean_term_u2203_____x2c___00__closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_term_u2203_____x2c___00__closed__8;
static const lean_ctor_object l_Lean_term_u2203_____x2c___00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_termSatisfies__binder__pred_x25_____00__closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_term_u2203_____x2c___00__closed__9 = (const lean_object*)&l_Lean_term_u2203_____x2c___00__closed__9_value;
static lean_once_cell_t l_Lean_term_u2203_____x2c___00__closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_term_u2203_____x2c___00__closed__10;
static lean_once_cell_t l_Lean_term_u2203_____x2c___00__closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_term_u2203_____x2c___00__closed__11;
LEAN_EXPORT lean_object* l_Lean_term_u2203_____x2c__;
static const lean_string_object l_Lean_term_u2200_____x2c___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 9, .m_data = "term∀__,_"};
static const lean_object* l_Lean_term_u2200_____x2c___00__closed__0 = (const lean_object*)&l_Lean_term_u2200_____x2c___00__closed__0_value;
static const lean_ctor_object l_Lean_term_u2200_____x2c___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_binderPred_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_term_u2200_____x2c___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_term_u2200_____x2c___00__closed__1_value_aux_0),((lean_object*)&l_Lean_term_u2200_____x2c___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(124, 16, 227, 203, 159, 8, 82, 19)}};
static const lean_object* l_Lean_term_u2200_____x2c___00__closed__1 = (const lean_object*)&l_Lean_term_u2200_____x2c___00__closed__1_value;
static const lean_string_object l_Lean_term_u2200_____x2c___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 2, .m_data = "∀ "};
static const lean_object* l_Lean_term_u2200_____x2c___00__closed__2 = (const lean_object*)&l_Lean_term_u2200_____x2c___00__closed__2_value;
static const lean_ctor_object l_Lean_term_u2200_____x2c___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_term_u2200_____x2c___00__closed__2_value)}};
static const lean_object* l_Lean_term_u2200_____x2c___00__closed__3 = (const lean_object*)&l_Lean_term_u2200_____x2c___00__closed__3_value;
static lean_once_cell_t l_Lean_term_u2200_____x2c___00__closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_term_u2200_____x2c___00__closed__4;
static lean_once_cell_t l_Lean_term_u2200_____x2c___00__closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_term_u2200_____x2c___00__closed__5;
static lean_once_cell_t l_Lean_term_u2200_____x2c___00__closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_term_u2200_____x2c___00__closed__6;
static lean_once_cell_t l_Lean_term_u2200_____x2c___00__closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_term_u2200_____x2c___00__closed__7;
static lean_once_cell_t l_Lean_term_u2200_____x2c___00__closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_term_u2200_____x2c___00__closed__8;
LEAN_EXPORT lean_object* l_Lean_term_u2200_____x2c__;
static const lean_string_object l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "binderIdent"};
static const lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__0 = (const lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__0_value;
static const lean_ctor_object l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_binderPred_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__1_value_aux_0),((lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 194, 68, 106, 254, 181, 31, 191)}};
static const lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__1 = (const lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__1_value;
static const lean_string_object l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__2 = (const lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__2_value;
static const lean_ctor_object l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__3 = (const lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__3_value;
static const lean_string_object l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__4 = (const lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__4_value;
static const lean_ctor_object l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_binderPred_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__5_value_aux_0),((lean_object*)&l_Lean_binderPred_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__5_value_aux_1),((lean_object*)&l_Lean_binderPred_quot___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__5_value_aux_2),((lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__5 = (const lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__5_value;
static const lean_string_object l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 8, .m_data = "term∃_,_"};
static const lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__6 = (const lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__6_value;
static const lean_ctor_object l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(224, 105, 219, 112, 166, 139, 167, 161)}};
static const lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__7 = (const lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__7_value;
static const lean_string_object l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "∃"};
static const lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__8 = (const lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__8_value;
static const lean_string_object l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "explicitBinders"};
static const lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__9 = (const lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__9_value;
static const lean_ctor_object l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_binderPred_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__10_value_aux_0),((lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(167, 149, 127, 13, 202, 239, 226, 94)}};
static const lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__10 = (const lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__10_value;
static const lean_string_object l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "unbracketedExplicitBinders"};
static const lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__11 = (const lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__11_value;
static const lean_ctor_object l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_binderPred_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__12_value_aux_0),((lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__11_value),LEAN_SCALAR_PTR_LITERAL(187, 220, 119, 82, 242, 112, 119, 200)}};
static const lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__12 = (const lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__12_value;
static const lean_string_object l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__13 = (const lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__13_value;
static const lean_ctor_object l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__13_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__14 = (const lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__14_value;
static const lean_string_object l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__15 = (const lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__15_value;
static lean_once_cell_t l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__16;
static const lean_ctor_object l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__17 = (const lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__17_value;
static lean_once_cell_t l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__18;
static const lean_string_object l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__19 = (const lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__19_value;
static const lean_string_object l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 7, .m_data = "term_∧_"};
static const lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__20 = (const lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__20_value;
static const lean_ctor_object l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(213, 224, 85, 99, 168, 124, 84, 223)}};
static const lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__21 = (const lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__21_value;
static const lean_string_object l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "satisfies_binder_pred%"};
static const lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__22 = (const lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__22_value;
static const lean_string_object l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "∧"};
static const lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__23 = (const lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__23_value;
LEAN_EXPORT lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "forall"};
static const lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__0 = (const lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__0_value;
static const lean_ctor_object l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_binderPred_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__1_value_aux_0),((lean_object*)&l_Lean_binderPred_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__1_value_aux_1),((lean_object*)&l_Lean_binderPred_quot___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__1_value_aux_2),((lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(195, 142, 115, 15, 55, 103, 31, 115)}};
static const lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__1 = (const lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__1_value;
static const lean_string_object l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "∀"};
static const lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__2 = (const lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__2_value;
static const lean_string_object l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "arrow"};
static const lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__3 = (const lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__3_value;
static const lean_ctor_object l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_binderPred_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__4_value_aux_0),((lean_object*)&l_Lean_binderPred_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__4_value_aux_1),((lean_object*)&l_Lean_binderPred_quot___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__4_value_aux_2),((lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(182, 146, 143, 73, 122, 115, 5, 207)}};
static const lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__4 = (const lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__4_value;
static const lean_string_object l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "→"};
static const lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__5 = (const lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__5_value;
LEAN_EXPORT lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_binderPred_x3e___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "binderPred>_"};
static const lean_object* l_Lean_binderPred_x3e___00__closed__0 = (const lean_object*)&l_Lean_binderPred_x3e___00__closed__0_value;
static const lean_ctor_object l_Lean_binderPred_x3e___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_binderPred_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_binderPred_x3e___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_binderPred_x3e___00__closed__1_value_aux_0),((lean_object*)&l_Lean_binderPred_x3e___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(140, 244, 246, 184, 111, 78, 213, 47)}};
static const lean_object* l_Lean_binderPred_x3e___00__closed__1 = (const lean_object*)&l_Lean_binderPred_x3e___00__closed__1_value;
static const lean_string_object l_Lean_binderPred_x3e___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " > "};
static const lean_object* l_Lean_binderPred_x3e___00__closed__2 = (const lean_object*)&l_Lean_binderPred_x3e___00__closed__2_value;
static const lean_ctor_object l_Lean_binderPred_x3e___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_binderPred_x3e___00__closed__2_value)}};
static const lean_object* l_Lean_binderPred_x3e___00__closed__3 = (const lean_object*)&l_Lean_binderPred_x3e___00__closed__3_value;
static const lean_ctor_object l_Lean_binderPred_x3e___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_binderPred_quot___closed__8_value),((lean_object*)&l_Lean_binderPred_x3e___00__closed__3_value),((lean_object*)&l_Lean_term_u2203_____x2c___00__closed__9_value)}};
static const lean_object* l_Lean_binderPred_x3e___00__closed__4 = (const lean_object*)&l_Lean_binderPred_x3e___00__closed__4_value;
static const lean_ctor_object l_Lean_binderPred_x3e___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_binderPred_x3e___00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_binderPred_x3e___00__closed__4_value)}};
static const lean_object* l_Lean_binderPred_x3e___00__closed__5 = (const lean_object*)&l_Lean_binderPred_x3e___00__closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_binderPred_x3e__ = (const lean_object*)&l_Lean_binderPred_x3e___00__closed__5_value;
static const lean_string_object l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "term_>_"};
static const lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______1___closed__0 = (const lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______1___closed__0_value;
static const lean_ctor_object l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(21, 139, 32, 245, 79, 44, 200, 27)}};
static const lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______1___closed__1 = (const lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______1___closed__1_value;
static const lean_string_object l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ">"};
static const lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______1___closed__2 = (const lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_binderPred_u2265___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 12, .m_data = "binderPred≥_"};
static const lean_object* l_Lean_binderPred_u2265___00__closed__0 = (const lean_object*)&l_Lean_binderPred_u2265___00__closed__0_value;
static const lean_ctor_object l_Lean_binderPred_u2265___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_binderPred_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_binderPred_u2265___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_binderPred_u2265___00__closed__1_value_aux_0),((lean_object*)&l_Lean_binderPred_u2265___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 139, 67, 46, 49, 133, 157, 246)}};
static const lean_object* l_Lean_binderPred_u2265___00__closed__1 = (const lean_object*)&l_Lean_binderPred_u2265___00__closed__1_value;
static const lean_string_object l_Lean_binderPred_u2265___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 3, .m_data = " ≥ "};
static const lean_object* l_Lean_binderPred_u2265___00__closed__2 = (const lean_object*)&l_Lean_binderPred_u2265___00__closed__2_value;
static const lean_ctor_object l_Lean_binderPred_u2265___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_binderPred_u2265___00__closed__2_value)}};
static const lean_object* l_Lean_binderPred_u2265___00__closed__3 = (const lean_object*)&l_Lean_binderPred_u2265___00__closed__3_value;
static const lean_ctor_object l_Lean_binderPred_u2265___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_binderPred_quot___closed__8_value),((lean_object*)&l_Lean_binderPred_u2265___00__closed__3_value),((lean_object*)&l_Lean_term_u2203_____x2c___00__closed__9_value)}};
static const lean_object* l_Lean_binderPred_u2265___00__closed__4 = (const lean_object*)&l_Lean_binderPred_u2265___00__closed__4_value;
static const lean_ctor_object l_Lean_binderPred_u2265___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_binderPred_u2265___00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_binderPred_u2265___00__closed__4_value)}};
static const lean_object* l_Lean_binderPred_u2265___00__closed__5 = (const lean_object*)&l_Lean_binderPred_u2265___00__closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_binderPred_u2265__ = (const lean_object*)&l_Lean_binderPred_u2265___00__closed__5_value;
static const lean_string_object l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 7, .m_data = "term_≥_"};
static const lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______2___closed__0 = (const lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______2___closed__0_value;
static const lean_ctor_object l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(58, 65, 30, 214, 7, 203, 184, 211)}};
static const lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______2___closed__1 = (const lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______2___closed__1_value;
static const lean_string_object l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "≥"};
static const lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______2___closed__2 = (const lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______2___closed__2_value;
LEAN_EXPORT lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_binderPred_x3c___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "binderPred<_"};
static const lean_object* l_Lean_binderPred_x3c___00__closed__0 = (const lean_object*)&l_Lean_binderPred_x3c___00__closed__0_value;
static const lean_ctor_object l_Lean_binderPred_x3c___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_binderPred_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_binderPred_x3c___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_binderPred_x3c___00__closed__1_value_aux_0),((lean_object*)&l_Lean_binderPred_x3c___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(87, 122, 58, 108, 39, 32, 195, 29)}};
static const lean_object* l_Lean_binderPred_x3c___00__closed__1 = (const lean_object*)&l_Lean_binderPred_x3c___00__closed__1_value;
static const lean_string_object l_Lean_binderPred_x3c___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " < "};
static const lean_object* l_Lean_binderPred_x3c___00__closed__2 = (const lean_object*)&l_Lean_binderPred_x3c___00__closed__2_value;
static const lean_ctor_object l_Lean_binderPred_x3c___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_binderPred_x3c___00__closed__2_value)}};
static const lean_object* l_Lean_binderPred_x3c___00__closed__3 = (const lean_object*)&l_Lean_binderPred_x3c___00__closed__3_value;
static const lean_ctor_object l_Lean_binderPred_x3c___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_binderPred_quot___closed__8_value),((lean_object*)&l_Lean_binderPred_x3c___00__closed__3_value),((lean_object*)&l_Lean_term_u2203_____x2c___00__closed__9_value)}};
static const lean_object* l_Lean_binderPred_x3c___00__closed__4 = (const lean_object*)&l_Lean_binderPred_x3c___00__closed__4_value;
static const lean_ctor_object l_Lean_binderPred_x3c___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_binderPred_x3c___00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_binderPred_x3c___00__closed__4_value)}};
static const lean_object* l_Lean_binderPred_x3c___00__closed__5 = (const lean_object*)&l_Lean_binderPred_x3c___00__closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_binderPred_x3c__ = (const lean_object*)&l_Lean_binderPred_x3c___00__closed__5_value;
static const lean_string_object l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "term_<_"};
static const lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______3___closed__0 = (const lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______3___closed__0_value;
static const lean_ctor_object l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(192, 242, 106, 74, 199, 131, 133, 95)}};
static const lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______3___closed__1 = (const lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______3___closed__1_value;
static const lean_string_object l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "<"};
static const lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______3___closed__2 = (const lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______3___closed__2_value;
LEAN_EXPORT lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______3___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_binderPred_u2264___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 12, .m_data = "binderPred≤_"};
static const lean_object* l_Lean_binderPred_u2264___00__closed__0 = (const lean_object*)&l_Lean_binderPred_u2264___00__closed__0_value;
static const lean_ctor_object l_Lean_binderPred_u2264___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_binderPred_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_binderPred_u2264___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_binderPred_u2264___00__closed__1_value_aux_0),((lean_object*)&l_Lean_binderPred_u2264___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(118, 254, 52, 209, 56, 53, 218, 188)}};
static const lean_object* l_Lean_binderPred_u2264___00__closed__1 = (const lean_object*)&l_Lean_binderPred_u2264___00__closed__1_value;
static const lean_string_object l_Lean_binderPred_u2264___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 3, .m_data = " ≤ "};
static const lean_object* l_Lean_binderPred_u2264___00__closed__2 = (const lean_object*)&l_Lean_binderPred_u2264___00__closed__2_value;
static const lean_ctor_object l_Lean_binderPred_u2264___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_binderPred_u2264___00__closed__2_value)}};
static const lean_object* l_Lean_binderPred_u2264___00__closed__3 = (const lean_object*)&l_Lean_binderPred_u2264___00__closed__3_value;
static const lean_ctor_object l_Lean_binderPred_u2264___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_binderPred_quot___closed__8_value),((lean_object*)&l_Lean_binderPred_u2264___00__closed__3_value),((lean_object*)&l_Lean_term_u2203_____x2c___00__closed__9_value)}};
static const lean_object* l_Lean_binderPred_u2264___00__closed__4 = (const lean_object*)&l_Lean_binderPred_u2264___00__closed__4_value;
static const lean_ctor_object l_Lean_binderPred_u2264___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_binderPred_u2264___00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_binderPred_u2264___00__closed__4_value)}};
static const lean_object* l_Lean_binderPred_u2264___00__closed__5 = (const lean_object*)&l_Lean_binderPred_u2264___00__closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_binderPred_u2264__ = (const lean_object*)&l_Lean_binderPred_u2264___00__closed__5_value;
static const lean_string_object l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 7, .m_data = "term_≤_"};
static const lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______4___closed__0 = (const lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______4___closed__0_value;
static const lean_ctor_object l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 3, 61, 112, 38, 138, 106, 121)}};
static const lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______4___closed__1 = (const lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______4___closed__1_value;
static const lean_string_object l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "≤"};
static const lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______4___closed__2 = (const lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______4___closed__2_value;
LEAN_EXPORT lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______4___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_binderPred_u2260___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 12, .m_data = "binderPred≠_"};
static const lean_object* l_Lean_binderPred_u2260___00__closed__0 = (const lean_object*)&l_Lean_binderPred_u2260___00__closed__0_value;
static const lean_ctor_object l_Lean_binderPred_u2260___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_binderPred_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_binderPred_u2260___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_binderPred_u2260___00__closed__1_value_aux_0),((lean_object*)&l_Lean_binderPred_u2260___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(39, 40, 245, 52, 138, 78, 140, 19)}};
static const lean_object* l_Lean_binderPred_u2260___00__closed__1 = (const lean_object*)&l_Lean_binderPred_u2260___00__closed__1_value;
static const lean_string_object l_Lean_binderPred_u2260___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 3, .m_data = " ≠ "};
static const lean_object* l_Lean_binderPred_u2260___00__closed__2 = (const lean_object*)&l_Lean_binderPred_u2260___00__closed__2_value;
static const lean_ctor_object l_Lean_binderPred_u2260___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_binderPred_u2260___00__closed__2_value)}};
static const lean_object* l_Lean_binderPred_u2260___00__closed__3 = (const lean_object*)&l_Lean_binderPred_u2260___00__closed__3_value;
static const lean_ctor_object l_Lean_binderPred_u2260___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_binderPred_quot___closed__8_value),((lean_object*)&l_Lean_binderPred_u2260___00__closed__3_value),((lean_object*)&l_Lean_term_u2203_____x2c___00__closed__9_value)}};
static const lean_object* l_Lean_binderPred_u2260___00__closed__4 = (const lean_object*)&l_Lean_binderPred_u2260___00__closed__4_value;
static const lean_ctor_object l_Lean_binderPred_u2260___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_binderPred_u2260___00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_binderPred_u2260___00__closed__4_value)}};
static const lean_object* l_Lean_binderPred_u2260___00__closed__5 = (const lean_object*)&l_Lean_binderPred_u2260___00__closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_binderPred_u2260__ = (const lean_object*)&l_Lean_binderPred_u2260___00__closed__5_value;
static const lean_string_object l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 7, .m_data = "term_≠_"};
static const lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______5___closed__0 = (const lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______5___closed__0_value;
static const lean_ctor_object l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(120, 22, 203, 44, 60, 124, 87, 95)}};
static const lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______5___closed__1 = (const lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______5___closed__1_value;
static const lean_string_object l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "≠"};
static const lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______5___closed__2 = (const lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______5___closed__2_value;
LEAN_EXPORT lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______5___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_binderPred_u2208___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 12, .m_data = "binderPred∈_"};
static const lean_object* l_Lean_binderPred_u2208___00__closed__0 = (const lean_object*)&l_Lean_binderPred_u2208___00__closed__0_value;
static const lean_ctor_object l_Lean_binderPred_u2208___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_binderPred_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_binderPred_u2208___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_binderPred_u2208___00__closed__1_value_aux_0),((lean_object*)&l_Lean_binderPred_u2208___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(150, 164, 254, 63, 76, 57, 126, 92)}};
static const lean_object* l_Lean_binderPred_u2208___00__closed__1 = (const lean_object*)&l_Lean_binderPred_u2208___00__closed__1_value;
static const lean_string_object l_Lean_binderPred_u2208___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 3, .m_data = " ∈ "};
static const lean_object* l_Lean_binderPred_u2208___00__closed__2 = (const lean_object*)&l_Lean_binderPred_u2208___00__closed__2_value;
static const lean_ctor_object l_Lean_binderPred_u2208___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_binderPred_u2208___00__closed__2_value)}};
static const lean_object* l_Lean_binderPred_u2208___00__closed__3 = (const lean_object*)&l_Lean_binderPred_u2208___00__closed__3_value;
static const lean_ctor_object l_Lean_binderPred_u2208___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_binderPred_quot___closed__8_value),((lean_object*)&l_Lean_binderPred_u2208___00__closed__3_value),((lean_object*)&l_Lean_term_u2203_____x2c___00__closed__9_value)}};
static const lean_object* l_Lean_binderPred_u2208___00__closed__4 = (const lean_object*)&l_Lean_binderPred_u2208___00__closed__4_value;
static const lean_ctor_object l_Lean_binderPred_u2208___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_binderPred_u2208___00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_binderPred_u2208___00__closed__4_value)}};
static const lean_object* l_Lean_binderPred_u2208___00__closed__5 = (const lean_object*)&l_Lean_binderPred_u2208___00__closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_binderPred_u2208__ = (const lean_object*)&l_Lean_binderPred_u2208___00__closed__5_value;
static const lean_string_object l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 7, .m_data = "term_∈_"};
static const lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______6___closed__0 = (const lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______6___closed__0_value;
static const lean_ctor_object l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______6___closed__0_value),LEAN_SCALAR_PTR_LITERAL(145, 149, 102, 29, 65, 152, 113, 144)}};
static const lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______6___closed__1 = (const lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______6___closed__1_value;
static const lean_string_object l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "∈"};
static const lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______6___closed__2 = (const lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______6___closed__2_value;
LEAN_EXPORT lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______6___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_binderPred_u2209___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 12, .m_data = "binderPred∉_"};
static const lean_object* l_Lean_binderPred_u2209___00__closed__0 = (const lean_object*)&l_Lean_binderPred_u2209___00__closed__0_value;
static const lean_ctor_object l_Lean_binderPred_u2209___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_binderPred_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_binderPred_u2209___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_binderPred_u2209___00__closed__1_value_aux_0),((lean_object*)&l_Lean_binderPred_u2209___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(147, 253, 164, 249, 200, 108, 121, 70)}};
static const lean_object* l_Lean_binderPred_u2209___00__closed__1 = (const lean_object*)&l_Lean_binderPred_u2209___00__closed__1_value;
static const lean_string_object l_Lean_binderPred_u2209___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 3, .m_data = " ∉ "};
static const lean_object* l_Lean_binderPred_u2209___00__closed__2 = (const lean_object*)&l_Lean_binderPred_u2209___00__closed__2_value;
static const lean_ctor_object l_Lean_binderPred_u2209___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_binderPred_u2209___00__closed__2_value)}};
static const lean_object* l_Lean_binderPred_u2209___00__closed__3 = (const lean_object*)&l_Lean_binderPred_u2209___00__closed__3_value;
static const lean_ctor_object l_Lean_binderPred_u2209___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_binderPred_quot___closed__8_value),((lean_object*)&l_Lean_binderPred_u2209___00__closed__3_value),((lean_object*)&l_Lean_term_u2203_____x2c___00__closed__9_value)}};
static const lean_object* l_Lean_binderPred_u2209___00__closed__4 = (const lean_object*)&l_Lean_binderPred_u2209___00__closed__4_value;
static const lean_ctor_object l_Lean_binderPred_u2209___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_binderPred_u2209___00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_binderPred_u2209___00__closed__4_value)}};
static const lean_object* l_Lean_binderPred_u2209___00__closed__5 = (const lean_object*)&l_Lean_binderPred_u2209___00__closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_binderPred_u2209__ = (const lean_object*)&l_Lean_binderPred_u2209___00__closed__5_value;
static const lean_string_object l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 7, .m_data = "term_∉_"};
static const lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______7___closed__0 = (const lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______7___closed__0_value;
static const lean_ctor_object l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______7___closed__0_value),LEAN_SCALAR_PTR_LITERAL(241, 191, 47, 82, 105, 120, 162, 72)}};
static const lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______7___closed__1 = (const lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______7___closed__1_value;
static const lean_string_object l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______7___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "∉"};
static const lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______7___closed__2 = (const lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______7___closed__2_value;
LEAN_EXPORT lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______7___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_binderPred_u2286___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 12, .m_data = "binderPred⊆_"};
static const lean_object* l_Lean_binderPred_u2286___00__closed__0 = (const lean_object*)&l_Lean_binderPred_u2286___00__closed__0_value;
static const lean_ctor_object l_Lean_binderPred_u2286___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_binderPred_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_binderPred_u2286___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_binderPred_u2286___00__closed__1_value_aux_0),((lean_object*)&l_Lean_binderPred_u2286___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(177, 23, 43, 221, 193, 123, 248, 62)}};
static const lean_object* l_Lean_binderPred_u2286___00__closed__1 = (const lean_object*)&l_Lean_binderPred_u2286___00__closed__1_value;
static const lean_string_object l_Lean_binderPred_u2286___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 3, .m_data = " ⊆ "};
static const lean_object* l_Lean_binderPred_u2286___00__closed__2 = (const lean_object*)&l_Lean_binderPred_u2286___00__closed__2_value;
static const lean_ctor_object l_Lean_binderPred_u2286___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_binderPred_u2286___00__closed__2_value)}};
static const lean_object* l_Lean_binderPred_u2286___00__closed__3 = (const lean_object*)&l_Lean_binderPred_u2286___00__closed__3_value;
static const lean_ctor_object l_Lean_binderPred_u2286___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_binderPred_quot___closed__8_value),((lean_object*)&l_Lean_binderPred_u2286___00__closed__3_value),((lean_object*)&l_Lean_term_u2203_____x2c___00__closed__9_value)}};
static const lean_object* l_Lean_binderPred_u2286___00__closed__4 = (const lean_object*)&l_Lean_binderPred_u2286___00__closed__4_value;
static const lean_ctor_object l_Lean_binderPred_u2286___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_binderPred_u2286___00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_binderPred_u2286___00__closed__4_value)}};
static const lean_object* l_Lean_binderPred_u2286___00__closed__5 = (const lean_object*)&l_Lean_binderPred_u2286___00__closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_binderPred_u2286__ = (const lean_object*)&l_Lean_binderPred_u2286___00__closed__5_value;
static const lean_string_object l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 7, .m_data = "term_⊆_"};
static const lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______8___closed__0 = (const lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______8___closed__0_value;
static const lean_ctor_object l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______8___closed__0_value),LEAN_SCALAR_PTR_LITERAL(17, 202, 90, 218, 225, 73, 214, 71)}};
static const lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______8___closed__1 = (const lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______8___closed__1_value;
static const lean_string_object l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______8___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⊆"};
static const lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______8___closed__2 = (const lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______8___closed__2_value;
LEAN_EXPORT lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______8___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_binderPred_u2282___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 12, .m_data = "binderPred⊂_"};
static const lean_object* l_Lean_binderPred_u2282___00__closed__0 = (const lean_object*)&l_Lean_binderPred_u2282___00__closed__0_value;
static const lean_ctor_object l_Lean_binderPred_u2282___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_binderPred_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_binderPred_u2282___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_binderPred_u2282___00__closed__1_value_aux_0),((lean_object*)&l_Lean_binderPred_u2282___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(43, 93, 221, 41, 188, 55, 153, 107)}};
static const lean_object* l_Lean_binderPred_u2282___00__closed__1 = (const lean_object*)&l_Lean_binderPred_u2282___00__closed__1_value;
static const lean_string_object l_Lean_binderPred_u2282___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 3, .m_data = " ⊂ "};
static const lean_object* l_Lean_binderPred_u2282___00__closed__2 = (const lean_object*)&l_Lean_binderPred_u2282___00__closed__2_value;
static const lean_ctor_object l_Lean_binderPred_u2282___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_binderPred_u2282___00__closed__2_value)}};
static const lean_object* l_Lean_binderPred_u2282___00__closed__3 = (const lean_object*)&l_Lean_binderPred_u2282___00__closed__3_value;
static const lean_ctor_object l_Lean_binderPred_u2282___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_binderPred_quot___closed__8_value),((lean_object*)&l_Lean_binderPred_u2282___00__closed__3_value),((lean_object*)&l_Lean_term_u2203_____x2c___00__closed__9_value)}};
static const lean_object* l_Lean_binderPred_u2282___00__closed__4 = (const lean_object*)&l_Lean_binderPred_u2282___00__closed__4_value;
static const lean_ctor_object l_Lean_binderPred_u2282___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_binderPred_u2282___00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_binderPred_u2282___00__closed__4_value)}};
static const lean_object* l_Lean_binderPred_u2282___00__closed__5 = (const lean_object*)&l_Lean_binderPred_u2282___00__closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_binderPred_u2282__ = (const lean_object*)&l_Lean_binderPred_u2282___00__closed__5_value;
static const lean_string_object l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 7, .m_data = "term_⊂_"};
static const lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______9___closed__0 = (const lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______9___closed__0_value;
static const lean_ctor_object l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______9___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______9___closed__0_value),LEAN_SCALAR_PTR_LITERAL(168, 36, 104, 26, 7, 158, 117, 91)}};
static const lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______9___closed__1 = (const lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______9___closed__1_value;
static const lean_string_object l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______9___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⊂"};
static const lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______9___closed__2 = (const lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______9___closed__2_value;
LEAN_EXPORT lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______9___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_binderPred_u2287___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 12, .m_data = "binderPred⊇_"};
static const lean_object* l_Lean_binderPred_u2287___00__closed__0 = (const lean_object*)&l_Lean_binderPred_u2287___00__closed__0_value;
static const lean_ctor_object l_Lean_binderPred_u2287___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_binderPred_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_binderPred_u2287___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_binderPred_u2287___00__closed__1_value_aux_0),((lean_object*)&l_Lean_binderPred_u2287___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(121, 205, 109, 198, 229, 195, 21, 21)}};
static const lean_object* l_Lean_binderPred_u2287___00__closed__1 = (const lean_object*)&l_Lean_binderPred_u2287___00__closed__1_value;
static const lean_string_object l_Lean_binderPred_u2287___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 3, .m_data = " ⊇ "};
static const lean_object* l_Lean_binderPred_u2287___00__closed__2 = (const lean_object*)&l_Lean_binderPred_u2287___00__closed__2_value;
static const lean_ctor_object l_Lean_binderPred_u2287___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_binderPred_u2287___00__closed__2_value)}};
static const lean_object* l_Lean_binderPred_u2287___00__closed__3 = (const lean_object*)&l_Lean_binderPred_u2287___00__closed__3_value;
static const lean_ctor_object l_Lean_binderPred_u2287___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_binderPred_quot___closed__8_value),((lean_object*)&l_Lean_binderPred_u2287___00__closed__3_value),((lean_object*)&l_Lean_term_u2203_____x2c___00__closed__9_value)}};
static const lean_object* l_Lean_binderPred_u2287___00__closed__4 = (const lean_object*)&l_Lean_binderPred_u2287___00__closed__4_value;
static const lean_ctor_object l_Lean_binderPred_u2287___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_binderPred_u2287___00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_binderPred_u2287___00__closed__4_value)}};
static const lean_object* l_Lean_binderPred_u2287___00__closed__5 = (const lean_object*)&l_Lean_binderPred_u2287___00__closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_binderPred_u2287__ = (const lean_object*)&l_Lean_binderPred_u2287___00__closed__5_value;
static const lean_string_object l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______10___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 7, .m_data = "term_⊇_"};
static const lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______10___closed__0 = (const lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______10___closed__0_value;
static const lean_ctor_object l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______10___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______10___closed__0_value),LEAN_SCALAR_PTR_LITERAL(126, 48, 9, 251, 76, 50, 57, 116)}};
static const lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______10___closed__1 = (const lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______10___closed__1_value;
static const lean_string_object l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______10___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⊇"};
static const lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______10___closed__2 = (const lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______10___closed__2_value;
LEAN_EXPORT lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______10___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_binderPred_u2283___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 12, .m_data = "binderPred⊃_"};
static const lean_object* l_Lean_binderPred_u2283___00__closed__0 = (const lean_object*)&l_Lean_binderPred_u2283___00__closed__0_value;
static const lean_ctor_object l_Lean_binderPred_u2283___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_binderPred_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_binderPred_u2283___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_binderPred_u2283___00__closed__1_value_aux_0),((lean_object*)&l_Lean_binderPred_u2283___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(227, 228, 155, 154, 179, 5, 240, 181)}};
static const lean_object* l_Lean_binderPred_u2283___00__closed__1 = (const lean_object*)&l_Lean_binderPred_u2283___00__closed__1_value;
static const lean_string_object l_Lean_binderPred_u2283___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 3, .m_data = " ⊃ "};
static const lean_object* l_Lean_binderPred_u2283___00__closed__2 = (const lean_object*)&l_Lean_binderPred_u2283___00__closed__2_value;
static const lean_ctor_object l_Lean_binderPred_u2283___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_binderPred_u2283___00__closed__2_value)}};
static const lean_object* l_Lean_binderPred_u2283___00__closed__3 = (const lean_object*)&l_Lean_binderPred_u2283___00__closed__3_value;
static const lean_ctor_object l_Lean_binderPred_u2283___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_binderPred_quot___closed__8_value),((lean_object*)&l_Lean_binderPred_u2283___00__closed__3_value),((lean_object*)&l_Lean_term_u2203_____x2c___00__closed__9_value)}};
static const lean_object* l_Lean_binderPred_u2283___00__closed__4 = (const lean_object*)&l_Lean_binderPred_u2283___00__closed__4_value;
static const lean_ctor_object l_Lean_binderPred_u2283___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_binderPred_u2283___00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_binderPred_u2283___00__closed__4_value)}};
static const lean_object* l_Lean_binderPred_u2283___00__closed__5 = (const lean_object*)&l_Lean_binderPred_u2283___00__closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_binderPred_u2283__ = (const lean_object*)&l_Lean_binderPred_u2283___00__closed__5_value;
static const lean_string_object l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 7, .m_data = "term_⊃_"};
static const lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______11___closed__0 = (const lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______11___closed__0_value;
static const lean_ctor_object l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______11___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______11___closed__0_value),LEAN_SCALAR_PTR_LITERAL(50, 217, 255, 107, 39, 224, 209, 40)}};
static const lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______11___closed__1 = (const lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______11___closed__1_value;
static const lean_string_object l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______11___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⊃"};
static const lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______11___closed__2 = (const lean_object*)&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______11___closed__2_value;
LEAN_EXPORT lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______11___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Parser_Category_binderPred(void){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = lean_box(0);
return v___x_45_;
}
}
static lean_object* _init_l_Lean_term_u2203_____x2c___00__closed__4(void){
_start:
{
lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_79_ = l_Lean_binderIdent;
v___x_80_ = ((lean_object*)(l_Lean_term_u2203_____x2c___00__closed__3));
v___x_81_ = ((lean_object*)(l_Lean_binderPred_quot___closed__8));
v___x_82_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_82_, 0, v___x_81_);
lean_ctor_set(v___x_82_, 1, v___x_80_);
lean_ctor_set(v___x_82_, 2, v___x_79_);
return v___x_82_;
}
}
static lean_object* _init_l_Lean_term_u2203_____x2c___00__closed__5(void){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_83_ = ((lean_object*)(l_Lean_binderPred_quot___closed__12));
v___x_84_ = lean_obj_once(&l_Lean_term_u2203_____x2c___00__closed__4, &l_Lean_term_u2203_____x2c___00__closed__4_once, _init_l_Lean_term_u2203_____x2c___00__closed__4);
v___x_85_ = ((lean_object*)(l_Lean_binderPred_quot___closed__8));
v___x_86_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_86_, 0, v___x_85_);
lean_ctor_set(v___x_86_, 1, v___x_84_);
lean_ctor_set(v___x_86_, 2, v___x_83_);
return v___x_86_;
}
}
static lean_object* _init_l_Lean_term_u2203_____x2c___00__closed__8(void){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_90_ = ((lean_object*)(l_Lean_term_u2203_____x2c___00__closed__7));
v___x_91_ = lean_obj_once(&l_Lean_term_u2203_____x2c___00__closed__5, &l_Lean_term_u2203_____x2c___00__closed__5_once, _init_l_Lean_term_u2203_____x2c___00__closed__5);
v___x_92_ = ((lean_object*)(l_Lean_binderPred_quot___closed__8));
v___x_93_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_93_, 0, v___x_92_);
lean_ctor_set(v___x_93_, 1, v___x_91_);
lean_ctor_set(v___x_93_, 2, v___x_90_);
return v___x_93_;
}
}
static lean_object* _init_l_Lean_term_u2203_____x2c___00__closed__10(void){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_97_ = ((lean_object*)(l_Lean_term_u2203_____x2c___00__closed__9));
v___x_98_ = lean_obj_once(&l_Lean_term_u2203_____x2c___00__closed__8, &l_Lean_term_u2203_____x2c___00__closed__8_once, _init_l_Lean_term_u2203_____x2c___00__closed__8);
v___x_99_ = ((lean_object*)(l_Lean_binderPred_quot___closed__8));
v___x_100_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_100_, 0, v___x_99_);
lean_ctor_set(v___x_100_, 1, v___x_98_);
lean_ctor_set(v___x_100_, 2, v___x_97_);
return v___x_100_;
}
}
static lean_object* _init_l_Lean_term_u2203_____x2c___00__closed__11(void){
_start:
{
lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_101_ = lean_obj_once(&l_Lean_term_u2203_____x2c___00__closed__10, &l_Lean_term_u2203_____x2c___00__closed__10_once, _init_l_Lean_term_u2203_____x2c___00__closed__10);
v___x_102_ = lean_unsigned_to_nat(1022u);
v___x_103_ = ((lean_object*)(l_Lean_term_u2203_____x2c___00__closed__1));
v___x_104_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_104_, 0, v___x_103_);
lean_ctor_set(v___x_104_, 1, v___x_102_);
lean_ctor_set(v___x_104_, 2, v___x_101_);
return v___x_104_;
}
}
static lean_object* _init_l_Lean_term_u2203_____x2c__(void){
_start:
{
lean_object* v___x_105_; 
v___x_105_ = lean_obj_once(&l_Lean_term_u2203_____x2c___00__closed__11, &l_Lean_term_u2203_____x2c___00__closed__11_once, _init_l_Lean_term_u2203_____x2c___00__closed__11);
return v___x_105_;
}
}
static lean_object* _init_l_Lean_term_u2200_____x2c___00__closed__4(void){
_start:
{
lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_113_ = l_Lean_binderIdent;
v___x_114_ = ((lean_object*)(l_Lean_term_u2200_____x2c___00__closed__3));
v___x_115_ = ((lean_object*)(l_Lean_binderPred_quot___closed__8));
v___x_116_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_116_, 0, v___x_115_);
lean_ctor_set(v___x_116_, 1, v___x_114_);
lean_ctor_set(v___x_116_, 2, v___x_113_);
return v___x_116_;
}
}
static lean_object* _init_l_Lean_term_u2200_____x2c___00__closed__5(void){
_start:
{
lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_117_ = ((lean_object*)(l_Lean_binderPred_quot___closed__12));
v___x_118_ = lean_obj_once(&l_Lean_term_u2200_____x2c___00__closed__4, &l_Lean_term_u2200_____x2c___00__closed__4_once, _init_l_Lean_term_u2200_____x2c___00__closed__4);
v___x_119_ = ((lean_object*)(l_Lean_binderPred_quot___closed__8));
v___x_120_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_120_, 0, v___x_119_);
lean_ctor_set(v___x_120_, 1, v___x_118_);
lean_ctor_set(v___x_120_, 2, v___x_117_);
return v___x_120_;
}
}
static lean_object* _init_l_Lean_term_u2200_____x2c___00__closed__6(void){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_121_ = ((lean_object*)(l_Lean_term_u2203_____x2c___00__closed__7));
v___x_122_ = lean_obj_once(&l_Lean_term_u2200_____x2c___00__closed__5, &l_Lean_term_u2200_____x2c___00__closed__5_once, _init_l_Lean_term_u2200_____x2c___00__closed__5);
v___x_123_ = ((lean_object*)(l_Lean_binderPred_quot___closed__8));
v___x_124_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_124_, 0, v___x_123_);
lean_ctor_set(v___x_124_, 1, v___x_122_);
lean_ctor_set(v___x_124_, 2, v___x_121_);
return v___x_124_;
}
}
static lean_object* _init_l_Lean_term_u2200_____x2c___00__closed__7(void){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_125_ = ((lean_object*)(l_Lean_term_u2203_____x2c___00__closed__9));
v___x_126_ = lean_obj_once(&l_Lean_term_u2200_____x2c___00__closed__6, &l_Lean_term_u2200_____x2c___00__closed__6_once, _init_l_Lean_term_u2200_____x2c___00__closed__6);
v___x_127_ = ((lean_object*)(l_Lean_binderPred_quot___closed__8));
v___x_128_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_128_, 0, v___x_127_);
lean_ctor_set(v___x_128_, 1, v___x_126_);
lean_ctor_set(v___x_128_, 2, v___x_125_);
return v___x_128_;
}
}
static lean_object* _init_l_Lean_term_u2200_____x2c___00__closed__8(void){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_129_ = lean_obj_once(&l_Lean_term_u2200_____x2c___00__closed__7, &l_Lean_term_u2200_____x2c___00__closed__7_once, _init_l_Lean_term_u2200_____x2c___00__closed__7);
v___x_130_ = lean_unsigned_to_nat(1022u);
v___x_131_ = ((lean_object*)(l_Lean_term_u2200_____x2c___00__closed__1));
v___x_132_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_132_, 0, v___x_131_);
lean_ctor_set(v___x_132_, 1, v___x_130_);
lean_ctor_set(v___x_132_, 2, v___x_129_);
return v___x_132_;
}
}
static lean_object* _init_l_Lean_term_u2200_____x2c__(void){
_start:
{
lean_object* v___x_133_; 
v___x_133_ = lean_obj_once(&l_Lean_term_u2200_____x2c___00__closed__8, &l_Lean_term_u2200_____x2c___00__closed__8_once, _init_l_Lean_term_u2200_____x2c___00__closed__8);
return v___x_133_;
}
}
static lean_object* _init_l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__16(void){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_163_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__15));
v___x_164_ = l_String_toRawSubstring_x27(v___x_163_);
return v___x_164_;
}
}
static lean_object* _init_l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__18(void){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = l_Array_mkArray0(lean_box(0));
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1(lean_object* v_x_174_, lean_object* v_a_175_, lean_object* v_a_176_){
_start:
{
lean_object* v___x_177_; uint8_t v___x_178_; 
v___x_177_ = ((lean_object*)(l_Lean_term_u2203_____x2c___00__closed__1));
lean_inc(v_x_174_);
v___x_178_ = l_Lean_Syntax_isOfKind(v_x_174_, v___x_177_);
if (v___x_178_ == 0)
{
lean_object* v___x_179_; lean_object* v___x_180_; 
lean_dec(v_x_174_);
v___x_179_ = lean_box(1);
v___x_180_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_180_, 0, v___x_179_);
lean_ctor_set(v___x_180_, 1, v_a_176_);
return v___x_180_;
}
else
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; uint8_t v___x_184_; 
v___x_181_ = lean_unsigned_to_nat(1u);
v___x_182_ = l_Lean_Syntax_getArg(v_x_174_, v___x_181_);
v___x_183_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__1));
lean_inc(v___x_182_);
v___x_184_ = l_Lean_Syntax_isOfKind(v___x_182_, v___x_183_);
if (v___x_184_ == 0)
{
lean_object* v___x_185_; lean_object* v___x_186_; 
lean_dec(v___x_182_);
lean_dec(v_x_174_);
v___x_185_ = lean_box(1);
v___x_186_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_186_, 0, v___x_185_);
lean_ctor_set(v___x_186_, 1, v_a_176_);
return v___x_186_;
}
else
{
lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; uint8_t v___x_190_; 
v___x_187_ = lean_unsigned_to_nat(0u);
v___x_188_ = l_Lean_Syntax_getArg(v___x_182_, v___x_187_);
lean_dec(v___x_182_);
v___x_189_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__3));
lean_inc(v___x_188_);
v___x_190_ = l_Lean_Syntax_isOfKind(v___x_188_, v___x_189_);
if (v___x_190_ == 0)
{
lean_object* v___x_191_; uint8_t v___x_192_; 
v___x_191_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__5));
v___x_192_ = l_Lean_Syntax_isOfKind(v___x_188_, v___x_191_);
if (v___x_192_ == 0)
{
lean_object* v___x_193_; lean_object* v___x_194_; 
lean_dec(v_x_174_);
v___x_193_ = lean_box(1);
v___x_194_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_194_, 0, v___x_193_);
lean_ctor_set(v___x_194_, 1, v_a_176_);
return v___x_194_;
}
else
{
lean_object* v_quotContext_195_; lean_object* v_currMacroScope_196_; lean_object* v_ref_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v_quotContext_195_ = lean_ctor_get(v_a_175_, 1);
v_currMacroScope_196_ = lean_ctor_get(v_a_175_, 2);
v_ref_197_ = lean_ctor_get(v_a_175_, 5);
v___x_198_ = lean_unsigned_to_nat(2u);
v___x_199_ = l_Lean_Syntax_getArg(v_x_174_, v___x_198_);
v___x_200_ = lean_unsigned_to_nat(4u);
v___x_201_ = l_Lean_Syntax_getArg(v_x_174_, v___x_200_);
lean_dec(v_x_174_);
v___x_202_ = l_Lean_SourceInfo_fromRef(v_ref_197_, v___x_190_);
v___x_203_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__7));
v___x_204_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__8));
lean_inc_n(v___x_202_, 12);
v___x_205_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_205_, 0, v___x_202_);
lean_ctor_set(v___x_205_, 1, v___x_204_);
v___x_206_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__10));
v___x_207_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__12));
v___x_208_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__14));
v___x_209_ = lean_obj_once(&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__16, &l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__16_once, _init_l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__16);
v___x_210_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__17));
lean_inc(v_currMacroScope_196_);
lean_inc(v_quotContext_195_);
v___x_211_ = l_Lean_addMacroScope(v_quotContext_195_, v___x_210_, v_currMacroScope_196_);
v___x_212_ = lean_box(0);
v___x_213_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_213_, 0, v___x_202_);
lean_ctor_set(v___x_213_, 1, v___x_209_);
lean_ctor_set(v___x_213_, 2, v___x_211_);
lean_ctor_set(v___x_213_, 3, v___x_212_);
lean_inc_ref(v___x_213_);
v___x_214_ = l_Lean_Syntax_node1(v___x_202_, v___x_183_, v___x_213_);
v___x_215_ = l_Lean_Syntax_node1(v___x_202_, v___x_208_, v___x_214_);
v___x_216_ = lean_obj_once(&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__18, &l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__18_once, _init_l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__18);
v___x_217_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_217_, 0, v___x_202_);
lean_ctor_set(v___x_217_, 1, v___x_208_);
lean_ctor_set(v___x_217_, 2, v___x_216_);
v___x_218_ = l_Lean_Syntax_node2(v___x_202_, v___x_207_, v___x_215_, v___x_217_);
v___x_219_ = l_Lean_Syntax_node1(v___x_202_, v___x_206_, v___x_218_);
v___x_220_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__19));
v___x_221_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_221_, 0, v___x_202_);
lean_ctor_set(v___x_221_, 1, v___x_220_);
v___x_222_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__21));
v___x_223_ = ((lean_object*)(l_Lean_termSatisfies__binder__pred_x25_____00__closed__1));
v___x_224_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__22));
v___x_225_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_225_, 0, v___x_202_);
lean_ctor_set(v___x_225_, 1, v___x_224_);
v___x_226_ = l_Lean_Syntax_node3(v___x_202_, v___x_223_, v___x_225_, v___x_213_, v___x_199_);
v___x_227_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__23));
v___x_228_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_228_, 0, v___x_202_);
lean_ctor_set(v___x_228_, 1, v___x_227_);
v___x_229_ = l_Lean_Syntax_node3(v___x_202_, v___x_222_, v___x_226_, v___x_228_, v___x_201_);
v___x_230_ = l_Lean_Syntax_node4(v___x_202_, v___x_203_, v___x_205_, v___x_219_, v___x_221_, v___x_229_);
v___x_231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_231_, 0, v___x_230_);
lean_ctor_set(v___x_231_, 1, v_a_176_);
return v___x_231_;
}
}
else
{
lean_object* v_ref_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; uint8_t v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v_ref_232_ = lean_ctor_get(v_a_175_, 5);
v___x_233_ = lean_unsigned_to_nat(2u);
v___x_234_ = l_Lean_Syntax_getArg(v_x_174_, v___x_233_);
v___x_235_ = lean_unsigned_to_nat(4u);
v___x_236_ = l_Lean_Syntax_getArg(v_x_174_, v___x_235_);
lean_dec(v_x_174_);
v___x_237_ = 0;
v___x_238_ = l_Lean_SourceInfo_fromRef(v_ref_232_, v___x_237_);
v___x_239_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__7));
v___x_240_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__8));
lean_inc_n(v___x_238_, 11);
v___x_241_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_241_, 0, v___x_238_);
lean_ctor_set(v___x_241_, 1, v___x_240_);
v___x_242_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__10));
v___x_243_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__12));
v___x_244_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__14));
lean_inc(v___x_188_);
v___x_245_ = l_Lean_Syntax_node1(v___x_238_, v___x_183_, v___x_188_);
v___x_246_ = l_Lean_Syntax_node1(v___x_238_, v___x_244_, v___x_245_);
v___x_247_ = lean_obj_once(&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__18, &l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__18_once, _init_l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__18);
v___x_248_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_248_, 0, v___x_238_);
lean_ctor_set(v___x_248_, 1, v___x_244_);
lean_ctor_set(v___x_248_, 2, v___x_247_);
v___x_249_ = l_Lean_Syntax_node2(v___x_238_, v___x_243_, v___x_246_, v___x_248_);
v___x_250_ = l_Lean_Syntax_node1(v___x_238_, v___x_242_, v___x_249_);
v___x_251_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__19));
v___x_252_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_252_, 0, v___x_238_);
lean_ctor_set(v___x_252_, 1, v___x_251_);
v___x_253_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__21));
v___x_254_ = ((lean_object*)(l_Lean_termSatisfies__binder__pred_x25_____00__closed__1));
v___x_255_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__22));
v___x_256_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_256_, 0, v___x_238_);
lean_ctor_set(v___x_256_, 1, v___x_255_);
v___x_257_ = l_Lean_Syntax_node3(v___x_238_, v___x_254_, v___x_256_, v___x_188_, v___x_234_);
v___x_258_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__23));
v___x_259_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_259_, 0, v___x_238_);
lean_ctor_set(v___x_259_, 1, v___x_258_);
v___x_260_ = l_Lean_Syntax_node3(v___x_238_, v___x_253_, v___x_257_, v___x_259_, v___x_236_);
v___x_261_ = l_Lean_Syntax_node4(v___x_238_, v___x_239_, v___x_241_, v___x_250_, v___x_252_, v___x_260_);
v___x_262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_262_, 0, v___x_261_);
lean_ctor_set(v___x_262_, 1, v_a_176_);
return v___x_262_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___boxed(lean_object* v_x_263_, lean_object* v_a_264_, lean_object* v_a_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1(v_x_263_, v_a_264_, v_a_265_);
lean_dec_ref(v_a_264_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1(lean_object* v_x_281_, lean_object* v_a_282_, lean_object* v_a_283_){
_start:
{
lean_object* v___x_284_; uint8_t v___x_285_; 
v___x_284_ = ((lean_object*)(l_Lean_term_u2200_____x2c___00__closed__1));
lean_inc(v_x_281_);
v___x_285_ = l_Lean_Syntax_isOfKind(v_x_281_, v___x_284_);
if (v___x_285_ == 0)
{
lean_object* v___x_286_; lean_object* v___x_287_; 
lean_dec(v_x_281_);
v___x_286_ = lean_box(1);
v___x_287_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_287_, 0, v___x_286_);
lean_ctor_set(v___x_287_, 1, v_a_283_);
return v___x_287_;
}
else
{
lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; uint8_t v___x_291_; 
v___x_288_ = lean_unsigned_to_nat(1u);
v___x_289_ = l_Lean_Syntax_getArg(v_x_281_, v___x_288_);
v___x_290_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__1));
lean_inc(v___x_289_);
v___x_291_ = l_Lean_Syntax_isOfKind(v___x_289_, v___x_290_);
if (v___x_291_ == 0)
{
lean_object* v___x_292_; lean_object* v___x_293_; 
lean_dec(v___x_289_);
lean_dec(v_x_281_);
v___x_292_ = lean_box(1);
v___x_293_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_293_, 0, v___x_292_);
lean_ctor_set(v___x_293_, 1, v_a_283_);
return v___x_293_;
}
else
{
lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; uint8_t v___x_297_; 
v___x_294_ = lean_unsigned_to_nat(0u);
v___x_295_ = l_Lean_Syntax_getArg(v___x_289_, v___x_294_);
lean_dec(v___x_289_);
v___x_296_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__3));
lean_inc(v___x_295_);
v___x_297_ = l_Lean_Syntax_isOfKind(v___x_295_, v___x_296_);
if (v___x_297_ == 0)
{
lean_object* v___x_298_; uint8_t v___x_299_; 
v___x_298_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__5));
v___x_299_ = l_Lean_Syntax_isOfKind(v___x_295_, v___x_298_);
if (v___x_299_ == 0)
{
lean_object* v___x_300_; lean_object* v___x_301_; 
lean_dec(v_x_281_);
v___x_300_ = lean_box(1);
v___x_301_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_301_, 0, v___x_300_);
lean_ctor_set(v___x_301_, 1, v_a_283_);
return v___x_301_;
}
else
{
lean_object* v_quotContext_302_; lean_object* v_currMacroScope_303_; lean_object* v_ref_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v_quotContext_302_ = lean_ctor_get(v_a_282_, 1);
v_currMacroScope_303_ = lean_ctor_get(v_a_282_, 2);
v_ref_304_ = lean_ctor_get(v_a_282_, 5);
v___x_305_ = lean_unsigned_to_nat(2u);
v___x_306_ = l_Lean_Syntax_getArg(v_x_281_, v___x_305_);
v___x_307_ = lean_unsigned_to_nat(4u);
v___x_308_ = l_Lean_Syntax_getArg(v_x_281_, v___x_307_);
lean_dec(v_x_281_);
v___x_309_ = l_Lean_SourceInfo_fromRef(v_ref_304_, v___x_297_);
v___x_310_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__1));
v___x_311_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__2));
lean_inc_n(v___x_309_, 9);
v___x_312_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_312_, 0, v___x_309_);
lean_ctor_set(v___x_312_, 1, v___x_311_);
v___x_313_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__14));
v___x_314_ = lean_obj_once(&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__16, &l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__16_once, _init_l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__16);
v___x_315_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__17));
lean_inc(v_currMacroScope_303_);
lean_inc(v_quotContext_302_);
v___x_316_ = l_Lean_addMacroScope(v_quotContext_302_, v___x_315_, v_currMacroScope_303_);
v___x_317_ = lean_box(0);
v___x_318_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_318_, 0, v___x_309_);
lean_ctor_set(v___x_318_, 1, v___x_314_);
lean_ctor_set(v___x_318_, 2, v___x_316_);
lean_ctor_set(v___x_318_, 3, v___x_317_);
lean_inc_ref(v___x_318_);
v___x_319_ = l_Lean_Syntax_node1(v___x_309_, v___x_313_, v___x_318_);
v___x_320_ = lean_obj_once(&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__18, &l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__18_once, _init_l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__18);
v___x_321_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_321_, 0, v___x_309_);
lean_ctor_set(v___x_321_, 1, v___x_313_);
lean_ctor_set(v___x_321_, 2, v___x_320_);
v___x_322_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__19));
v___x_323_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_323_, 0, v___x_309_);
lean_ctor_set(v___x_323_, 1, v___x_322_);
v___x_324_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__4));
v___x_325_ = ((lean_object*)(l_Lean_termSatisfies__binder__pred_x25_____00__closed__1));
v___x_326_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__22));
v___x_327_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_327_, 0, v___x_309_);
lean_ctor_set(v___x_327_, 1, v___x_326_);
v___x_328_ = l_Lean_Syntax_node3(v___x_309_, v___x_325_, v___x_327_, v___x_318_, v___x_306_);
v___x_329_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__5));
v___x_330_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_330_, 0, v___x_309_);
lean_ctor_set(v___x_330_, 1, v___x_329_);
v___x_331_ = l_Lean_Syntax_node3(v___x_309_, v___x_324_, v___x_328_, v___x_330_, v___x_308_);
v___x_332_ = l_Lean_Syntax_node5(v___x_309_, v___x_310_, v___x_312_, v___x_319_, v___x_321_, v___x_323_, v___x_331_);
v___x_333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_333_, 0, v___x_332_);
lean_ctor_set(v___x_333_, 1, v_a_283_);
return v___x_333_;
}
}
else
{
lean_object* v_ref_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; uint8_t v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
v_ref_334_ = lean_ctor_get(v_a_282_, 5);
v___x_335_ = lean_unsigned_to_nat(2u);
v___x_336_ = l_Lean_Syntax_getArg(v_x_281_, v___x_335_);
v___x_337_ = lean_unsigned_to_nat(4u);
v___x_338_ = l_Lean_Syntax_getArg(v_x_281_, v___x_337_);
lean_dec(v_x_281_);
v___x_339_ = 0;
v___x_340_ = l_Lean_SourceInfo_fromRef(v_ref_334_, v___x_339_);
v___x_341_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__1));
v___x_342_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__2));
lean_inc_n(v___x_340_, 8);
v___x_343_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_343_, 0, v___x_340_);
lean_ctor_set(v___x_343_, 1, v___x_342_);
v___x_344_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__14));
lean_inc(v___x_295_);
v___x_345_ = l_Lean_Syntax_node1(v___x_340_, v___x_344_, v___x_295_);
v___x_346_ = lean_obj_once(&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__18, &l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__18_once, _init_l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__18);
v___x_347_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_347_, 0, v___x_340_);
lean_ctor_set(v___x_347_, 1, v___x_344_);
lean_ctor_set(v___x_347_, 2, v___x_346_);
v___x_348_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__19));
v___x_349_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_349_, 0, v___x_340_);
lean_ctor_set(v___x_349_, 1, v___x_348_);
v___x_350_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__4));
v___x_351_ = ((lean_object*)(l_Lean_termSatisfies__binder__pred_x25_____00__closed__1));
v___x_352_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__22));
v___x_353_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_353_, 0, v___x_340_);
lean_ctor_set(v___x_353_, 1, v___x_352_);
v___x_354_ = l_Lean_Syntax_node3(v___x_340_, v___x_351_, v___x_353_, v___x_295_, v___x_336_);
v___x_355_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__5));
v___x_356_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_356_, 0, v___x_340_);
lean_ctor_set(v___x_356_, 1, v___x_355_);
v___x_357_ = l_Lean_Syntax_node3(v___x_340_, v___x_350_, v___x_354_, v___x_356_, v___x_338_);
v___x_358_ = l_Lean_Syntax_node5(v___x_340_, v___x_341_, v___x_343_, v___x_345_, v___x_347_, v___x_349_, v___x_357_);
v___x_359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_359_, 0, v___x_358_);
lean_ctor_set(v___x_359_, 1, v_a_283_);
return v___x_359_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___boxed(lean_object* v_x_360_, lean_object* v_a_361_, lean_object* v_a_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1(v_x_360_, v_a_361_, v_a_362_);
lean_dec_ref(v_a_361_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______1(lean_object* v_x_384_, lean_object* v_a_385_, lean_object* v_a_386_){
_start:
{
lean_object* v___x_387_; uint8_t v___x_388_; 
v___x_387_ = ((lean_object*)(l_Lean_termSatisfies__binder__pred_x25_____00__closed__1));
lean_inc(v_x_384_);
v___x_388_ = l_Lean_Syntax_isOfKind(v_x_384_, v___x_387_);
if (v___x_388_ == 0)
{
lean_object* v___x_389_; lean_object* v___x_390_; 
lean_dec(v_x_384_);
v___x_389_ = lean_box(1);
v___x_390_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_390_, 0, v___x_389_);
lean_ctor_set(v___x_390_, 1, v_a_386_);
return v___x_390_;
}
else
{
lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; uint8_t v___x_394_; 
v___x_391_ = lean_unsigned_to_nat(2u);
v___x_392_ = l_Lean_Syntax_getArg(v_x_384_, v___x_391_);
v___x_393_ = ((lean_object*)(l_Lean_binderPred_x3e___00__closed__1));
lean_inc(v___x_392_);
v___x_394_ = l_Lean_Syntax_isOfKind(v___x_392_, v___x_393_);
if (v___x_394_ == 0)
{
lean_object* v___x_395_; lean_object* v___x_396_; 
lean_dec(v___x_392_);
lean_dec(v_x_384_);
v___x_395_ = lean_box(1);
v___x_396_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_396_, 0, v___x_395_);
lean_ctor_set(v___x_396_, 1, v_a_386_);
return v___x_396_;
}
else
{
lean_object* v_ref_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; uint8_t v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v_ref_397_ = lean_ctor_get(v_a_385_, 5);
v___x_398_ = lean_unsigned_to_nat(1u);
v___x_399_ = l_Lean_Syntax_getArg(v_x_384_, v___x_398_);
lean_dec(v_x_384_);
v___x_400_ = l_Lean_Syntax_getArg(v___x_392_, v___x_398_);
lean_dec(v___x_392_);
v___x_401_ = 0;
v___x_402_ = l_Lean_SourceInfo_fromRef(v_ref_397_, v___x_401_);
v___x_403_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______1___closed__1));
v___x_404_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______1___closed__2));
lean_inc(v___x_402_);
v___x_405_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_405_, 0, v___x_402_);
lean_ctor_set(v___x_405_, 1, v___x_404_);
v___x_406_ = l_Lean_Syntax_node3(v___x_402_, v___x_403_, v___x_399_, v___x_405_, v___x_400_);
v___x_407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_407_, 0, v___x_406_);
lean_ctor_set(v___x_407_, 1, v_a_386_);
return v___x_407_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______1___boxed(lean_object* v_x_408_, lean_object* v_a_409_, lean_object* v_a_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______1(v_x_408_, v_a_409_, v_a_410_);
lean_dec_ref(v_a_409_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______2(lean_object* v_x_432_, lean_object* v_a_433_, lean_object* v_a_434_){
_start:
{
lean_object* v___x_435_; uint8_t v___x_436_; 
v___x_435_ = ((lean_object*)(l_Lean_termSatisfies__binder__pred_x25_____00__closed__1));
lean_inc(v_x_432_);
v___x_436_ = l_Lean_Syntax_isOfKind(v_x_432_, v___x_435_);
if (v___x_436_ == 0)
{
lean_object* v___x_437_; lean_object* v___x_438_; 
lean_dec(v_x_432_);
v___x_437_ = lean_box(1);
v___x_438_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_438_, 0, v___x_437_);
lean_ctor_set(v___x_438_, 1, v_a_434_);
return v___x_438_;
}
else
{
lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; uint8_t v___x_442_; 
v___x_439_ = lean_unsigned_to_nat(2u);
v___x_440_ = l_Lean_Syntax_getArg(v_x_432_, v___x_439_);
v___x_441_ = ((lean_object*)(l_Lean_binderPred_u2265___00__closed__1));
lean_inc(v___x_440_);
v___x_442_ = l_Lean_Syntax_isOfKind(v___x_440_, v___x_441_);
if (v___x_442_ == 0)
{
lean_object* v___x_443_; lean_object* v___x_444_; 
lean_dec(v___x_440_);
lean_dec(v_x_432_);
v___x_443_ = lean_box(1);
v___x_444_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_444_, 0, v___x_443_);
lean_ctor_set(v___x_444_, 1, v_a_434_);
return v___x_444_;
}
else
{
lean_object* v_ref_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; uint8_t v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
v_ref_445_ = lean_ctor_get(v_a_433_, 5);
v___x_446_ = lean_unsigned_to_nat(1u);
v___x_447_ = l_Lean_Syntax_getArg(v_x_432_, v___x_446_);
lean_dec(v_x_432_);
v___x_448_ = l_Lean_Syntax_getArg(v___x_440_, v___x_446_);
lean_dec(v___x_440_);
v___x_449_ = 0;
v___x_450_ = l_Lean_SourceInfo_fromRef(v_ref_445_, v___x_449_);
v___x_451_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______2___closed__1));
v___x_452_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______2___closed__2));
lean_inc(v___x_450_);
v___x_453_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_453_, 0, v___x_450_);
lean_ctor_set(v___x_453_, 1, v___x_452_);
v___x_454_ = l_Lean_Syntax_node3(v___x_450_, v___x_451_, v___x_447_, v___x_453_, v___x_448_);
v___x_455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_455_, 0, v___x_454_);
lean_ctor_set(v___x_455_, 1, v_a_434_);
return v___x_455_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______2___boxed(lean_object* v_x_456_, lean_object* v_a_457_, lean_object* v_a_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______2(v_x_456_, v_a_457_, v_a_458_);
lean_dec_ref(v_a_457_);
return v_res_459_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______3(lean_object* v_x_480_, lean_object* v_a_481_, lean_object* v_a_482_){
_start:
{
lean_object* v___x_483_; uint8_t v___x_484_; 
v___x_483_ = ((lean_object*)(l_Lean_termSatisfies__binder__pred_x25_____00__closed__1));
lean_inc(v_x_480_);
v___x_484_ = l_Lean_Syntax_isOfKind(v_x_480_, v___x_483_);
if (v___x_484_ == 0)
{
lean_object* v___x_485_; lean_object* v___x_486_; 
lean_dec(v_x_480_);
v___x_485_ = lean_box(1);
v___x_486_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_486_, 0, v___x_485_);
lean_ctor_set(v___x_486_, 1, v_a_482_);
return v___x_486_;
}
else
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; uint8_t v___x_490_; 
v___x_487_ = lean_unsigned_to_nat(2u);
v___x_488_ = l_Lean_Syntax_getArg(v_x_480_, v___x_487_);
v___x_489_ = ((lean_object*)(l_Lean_binderPred_x3c___00__closed__1));
lean_inc(v___x_488_);
v___x_490_ = l_Lean_Syntax_isOfKind(v___x_488_, v___x_489_);
if (v___x_490_ == 0)
{
lean_object* v___x_491_; lean_object* v___x_492_; 
lean_dec(v___x_488_);
lean_dec(v_x_480_);
v___x_491_ = lean_box(1);
v___x_492_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_492_, 0, v___x_491_);
lean_ctor_set(v___x_492_, 1, v_a_482_);
return v___x_492_;
}
else
{
lean_object* v_ref_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; uint8_t v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v_ref_493_ = lean_ctor_get(v_a_481_, 5);
v___x_494_ = lean_unsigned_to_nat(1u);
v___x_495_ = l_Lean_Syntax_getArg(v_x_480_, v___x_494_);
lean_dec(v_x_480_);
v___x_496_ = l_Lean_Syntax_getArg(v___x_488_, v___x_494_);
lean_dec(v___x_488_);
v___x_497_ = 0;
v___x_498_ = l_Lean_SourceInfo_fromRef(v_ref_493_, v___x_497_);
v___x_499_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______3___closed__1));
v___x_500_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______3___closed__2));
lean_inc(v___x_498_);
v___x_501_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_501_, 0, v___x_498_);
lean_ctor_set(v___x_501_, 1, v___x_500_);
v___x_502_ = l_Lean_Syntax_node3(v___x_498_, v___x_499_, v___x_495_, v___x_501_, v___x_496_);
v___x_503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_503_, 0, v___x_502_);
lean_ctor_set(v___x_503_, 1, v_a_482_);
return v___x_503_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______3___boxed(lean_object* v_x_504_, lean_object* v_a_505_, lean_object* v_a_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______3(v_x_504_, v_a_505_, v_a_506_);
lean_dec_ref(v_a_505_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______4(lean_object* v_x_528_, lean_object* v_a_529_, lean_object* v_a_530_){
_start:
{
lean_object* v___x_531_; uint8_t v___x_532_; 
v___x_531_ = ((lean_object*)(l_Lean_termSatisfies__binder__pred_x25_____00__closed__1));
lean_inc(v_x_528_);
v___x_532_ = l_Lean_Syntax_isOfKind(v_x_528_, v___x_531_);
if (v___x_532_ == 0)
{
lean_object* v___x_533_; lean_object* v___x_534_; 
lean_dec(v_x_528_);
v___x_533_ = lean_box(1);
v___x_534_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_534_, 0, v___x_533_);
lean_ctor_set(v___x_534_, 1, v_a_530_);
return v___x_534_;
}
else
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; uint8_t v___x_538_; 
v___x_535_ = lean_unsigned_to_nat(2u);
v___x_536_ = l_Lean_Syntax_getArg(v_x_528_, v___x_535_);
v___x_537_ = ((lean_object*)(l_Lean_binderPred_u2264___00__closed__1));
lean_inc(v___x_536_);
v___x_538_ = l_Lean_Syntax_isOfKind(v___x_536_, v___x_537_);
if (v___x_538_ == 0)
{
lean_object* v___x_539_; lean_object* v___x_540_; 
lean_dec(v___x_536_);
lean_dec(v_x_528_);
v___x_539_ = lean_box(1);
v___x_540_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_540_, 0, v___x_539_);
lean_ctor_set(v___x_540_, 1, v_a_530_);
return v___x_540_;
}
else
{
lean_object* v_ref_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; uint8_t v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
v_ref_541_ = lean_ctor_get(v_a_529_, 5);
v___x_542_ = lean_unsigned_to_nat(1u);
v___x_543_ = l_Lean_Syntax_getArg(v_x_528_, v___x_542_);
lean_dec(v_x_528_);
v___x_544_ = l_Lean_Syntax_getArg(v___x_536_, v___x_542_);
lean_dec(v___x_536_);
v___x_545_ = 0;
v___x_546_ = l_Lean_SourceInfo_fromRef(v_ref_541_, v___x_545_);
v___x_547_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______4___closed__1));
v___x_548_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______4___closed__2));
lean_inc(v___x_546_);
v___x_549_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_549_, 0, v___x_546_);
lean_ctor_set(v___x_549_, 1, v___x_548_);
v___x_550_ = l_Lean_Syntax_node3(v___x_546_, v___x_547_, v___x_543_, v___x_549_, v___x_544_);
v___x_551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_551_, 0, v___x_550_);
lean_ctor_set(v___x_551_, 1, v_a_530_);
return v___x_551_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______4___boxed(lean_object* v_x_552_, lean_object* v_a_553_, lean_object* v_a_554_){
_start:
{
lean_object* v_res_555_; 
v_res_555_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______4(v_x_552_, v_a_553_, v_a_554_);
lean_dec_ref(v_a_553_);
return v_res_555_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______5(lean_object* v_x_576_, lean_object* v_a_577_, lean_object* v_a_578_){
_start:
{
lean_object* v___x_579_; uint8_t v___x_580_; 
v___x_579_ = ((lean_object*)(l_Lean_termSatisfies__binder__pred_x25_____00__closed__1));
lean_inc(v_x_576_);
v___x_580_ = l_Lean_Syntax_isOfKind(v_x_576_, v___x_579_);
if (v___x_580_ == 0)
{
lean_object* v___x_581_; lean_object* v___x_582_; 
lean_dec(v_x_576_);
v___x_581_ = lean_box(1);
v___x_582_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_582_, 0, v___x_581_);
lean_ctor_set(v___x_582_, 1, v_a_578_);
return v___x_582_;
}
else
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; uint8_t v___x_586_; 
v___x_583_ = lean_unsigned_to_nat(2u);
v___x_584_ = l_Lean_Syntax_getArg(v_x_576_, v___x_583_);
v___x_585_ = ((lean_object*)(l_Lean_binderPred_u2260___00__closed__1));
lean_inc(v___x_584_);
v___x_586_ = l_Lean_Syntax_isOfKind(v___x_584_, v___x_585_);
if (v___x_586_ == 0)
{
lean_object* v___x_587_; lean_object* v___x_588_; 
lean_dec(v___x_584_);
lean_dec(v_x_576_);
v___x_587_ = lean_box(1);
v___x_588_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_588_, 0, v___x_587_);
lean_ctor_set(v___x_588_, 1, v_a_578_);
return v___x_588_;
}
else
{
lean_object* v_ref_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; uint8_t v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
v_ref_589_ = lean_ctor_get(v_a_577_, 5);
v___x_590_ = lean_unsigned_to_nat(1u);
v___x_591_ = l_Lean_Syntax_getArg(v_x_576_, v___x_590_);
lean_dec(v_x_576_);
v___x_592_ = l_Lean_Syntax_getArg(v___x_584_, v___x_590_);
lean_dec(v___x_584_);
v___x_593_ = 0;
v___x_594_ = l_Lean_SourceInfo_fromRef(v_ref_589_, v___x_593_);
v___x_595_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______5___closed__1));
v___x_596_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______5___closed__2));
lean_inc(v___x_594_);
v___x_597_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_597_, 0, v___x_594_);
lean_ctor_set(v___x_597_, 1, v___x_596_);
v___x_598_ = l_Lean_Syntax_node3(v___x_594_, v___x_595_, v___x_591_, v___x_597_, v___x_592_);
v___x_599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_599_, 0, v___x_598_);
lean_ctor_set(v___x_599_, 1, v_a_578_);
return v___x_599_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______5___boxed(lean_object* v_x_600_, lean_object* v_a_601_, lean_object* v_a_602_){
_start:
{
lean_object* v_res_603_; 
v_res_603_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______5(v_x_600_, v_a_601_, v_a_602_);
lean_dec_ref(v_a_601_);
return v_res_603_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______6(lean_object* v_x_624_, lean_object* v_a_625_, lean_object* v_a_626_){
_start:
{
lean_object* v___x_627_; uint8_t v___x_628_; 
v___x_627_ = ((lean_object*)(l_Lean_termSatisfies__binder__pred_x25_____00__closed__1));
lean_inc(v_x_624_);
v___x_628_ = l_Lean_Syntax_isOfKind(v_x_624_, v___x_627_);
if (v___x_628_ == 0)
{
lean_object* v___x_629_; lean_object* v___x_630_; 
lean_dec(v_x_624_);
v___x_629_ = lean_box(1);
v___x_630_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_630_, 0, v___x_629_);
lean_ctor_set(v___x_630_, 1, v_a_626_);
return v___x_630_;
}
else
{
lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; uint8_t v___x_634_; 
v___x_631_ = lean_unsigned_to_nat(2u);
v___x_632_ = l_Lean_Syntax_getArg(v_x_624_, v___x_631_);
v___x_633_ = ((lean_object*)(l_Lean_binderPred_u2208___00__closed__1));
lean_inc(v___x_632_);
v___x_634_ = l_Lean_Syntax_isOfKind(v___x_632_, v___x_633_);
if (v___x_634_ == 0)
{
lean_object* v___x_635_; lean_object* v___x_636_; 
lean_dec(v___x_632_);
lean_dec(v_x_624_);
v___x_635_ = lean_box(1);
v___x_636_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_636_, 0, v___x_635_);
lean_ctor_set(v___x_636_, 1, v_a_626_);
return v___x_636_;
}
else
{
lean_object* v_ref_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; uint8_t v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
v_ref_637_ = lean_ctor_get(v_a_625_, 5);
v___x_638_ = lean_unsigned_to_nat(1u);
v___x_639_ = l_Lean_Syntax_getArg(v_x_624_, v___x_638_);
lean_dec(v_x_624_);
v___x_640_ = l_Lean_Syntax_getArg(v___x_632_, v___x_638_);
lean_dec(v___x_632_);
v___x_641_ = 0;
v___x_642_ = l_Lean_SourceInfo_fromRef(v_ref_637_, v___x_641_);
v___x_643_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______6___closed__1));
v___x_644_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______6___closed__2));
lean_inc(v___x_642_);
v___x_645_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_645_, 0, v___x_642_);
lean_ctor_set(v___x_645_, 1, v___x_644_);
v___x_646_ = l_Lean_Syntax_node3(v___x_642_, v___x_643_, v___x_639_, v___x_645_, v___x_640_);
v___x_647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_647_, 0, v___x_646_);
lean_ctor_set(v___x_647_, 1, v_a_626_);
return v___x_647_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______6___boxed(lean_object* v_x_648_, lean_object* v_a_649_, lean_object* v_a_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______6(v_x_648_, v_a_649_, v_a_650_);
lean_dec_ref(v_a_649_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______7(lean_object* v_x_672_, lean_object* v_a_673_, lean_object* v_a_674_){
_start:
{
lean_object* v___x_675_; uint8_t v___x_676_; 
v___x_675_ = ((lean_object*)(l_Lean_termSatisfies__binder__pred_x25_____00__closed__1));
lean_inc(v_x_672_);
v___x_676_ = l_Lean_Syntax_isOfKind(v_x_672_, v___x_675_);
if (v___x_676_ == 0)
{
lean_object* v___x_677_; lean_object* v___x_678_; 
lean_dec(v_x_672_);
v___x_677_ = lean_box(1);
v___x_678_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_678_, 0, v___x_677_);
lean_ctor_set(v___x_678_, 1, v_a_674_);
return v___x_678_;
}
else
{
lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; uint8_t v___x_682_; 
v___x_679_ = lean_unsigned_to_nat(2u);
v___x_680_ = l_Lean_Syntax_getArg(v_x_672_, v___x_679_);
v___x_681_ = ((lean_object*)(l_Lean_binderPred_u2209___00__closed__1));
lean_inc(v___x_680_);
v___x_682_ = l_Lean_Syntax_isOfKind(v___x_680_, v___x_681_);
if (v___x_682_ == 0)
{
lean_object* v___x_683_; lean_object* v___x_684_; 
lean_dec(v___x_680_);
lean_dec(v_x_672_);
v___x_683_ = lean_box(1);
v___x_684_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_684_, 0, v___x_683_);
lean_ctor_set(v___x_684_, 1, v_a_674_);
return v___x_684_;
}
else
{
lean_object* v_ref_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; uint8_t v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; 
v_ref_685_ = lean_ctor_get(v_a_673_, 5);
v___x_686_ = lean_unsigned_to_nat(1u);
v___x_687_ = l_Lean_Syntax_getArg(v_x_672_, v___x_686_);
lean_dec(v_x_672_);
v___x_688_ = l_Lean_Syntax_getArg(v___x_680_, v___x_686_);
lean_dec(v___x_680_);
v___x_689_ = 0;
v___x_690_ = l_Lean_SourceInfo_fromRef(v_ref_685_, v___x_689_);
v___x_691_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______7___closed__1));
v___x_692_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______7___closed__2));
lean_inc(v___x_690_);
v___x_693_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_693_, 0, v___x_690_);
lean_ctor_set(v___x_693_, 1, v___x_692_);
v___x_694_ = l_Lean_Syntax_node3(v___x_690_, v___x_691_, v___x_687_, v___x_693_, v___x_688_);
v___x_695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_695_, 0, v___x_694_);
lean_ctor_set(v___x_695_, 1, v_a_674_);
return v___x_695_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______7___boxed(lean_object* v_x_696_, lean_object* v_a_697_, lean_object* v_a_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______7(v_x_696_, v_a_697_, v_a_698_);
lean_dec_ref(v_a_697_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______8(lean_object* v_x_720_, lean_object* v_a_721_, lean_object* v_a_722_){
_start:
{
lean_object* v___x_723_; uint8_t v___x_724_; 
v___x_723_ = ((lean_object*)(l_Lean_termSatisfies__binder__pred_x25_____00__closed__1));
lean_inc(v_x_720_);
v___x_724_ = l_Lean_Syntax_isOfKind(v_x_720_, v___x_723_);
if (v___x_724_ == 0)
{
lean_object* v___x_725_; lean_object* v___x_726_; 
lean_dec(v_x_720_);
v___x_725_ = lean_box(1);
v___x_726_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_726_, 0, v___x_725_);
lean_ctor_set(v___x_726_, 1, v_a_722_);
return v___x_726_;
}
else
{
lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; uint8_t v___x_730_; 
v___x_727_ = lean_unsigned_to_nat(2u);
v___x_728_ = l_Lean_Syntax_getArg(v_x_720_, v___x_727_);
v___x_729_ = ((lean_object*)(l_Lean_binderPred_u2286___00__closed__1));
lean_inc(v___x_728_);
v___x_730_ = l_Lean_Syntax_isOfKind(v___x_728_, v___x_729_);
if (v___x_730_ == 0)
{
lean_object* v___x_731_; lean_object* v___x_732_; 
lean_dec(v___x_728_);
lean_dec(v_x_720_);
v___x_731_ = lean_box(1);
v___x_732_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_732_, 0, v___x_731_);
lean_ctor_set(v___x_732_, 1, v_a_722_);
return v___x_732_;
}
else
{
lean_object* v_ref_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; uint8_t v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v_ref_733_ = lean_ctor_get(v_a_721_, 5);
v___x_734_ = lean_unsigned_to_nat(1u);
v___x_735_ = l_Lean_Syntax_getArg(v_x_720_, v___x_734_);
lean_dec(v_x_720_);
v___x_736_ = l_Lean_Syntax_getArg(v___x_728_, v___x_734_);
lean_dec(v___x_728_);
v___x_737_ = 0;
v___x_738_ = l_Lean_SourceInfo_fromRef(v_ref_733_, v___x_737_);
v___x_739_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______8___closed__1));
v___x_740_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______8___closed__2));
lean_inc(v___x_738_);
v___x_741_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_741_, 0, v___x_738_);
lean_ctor_set(v___x_741_, 1, v___x_740_);
v___x_742_ = l_Lean_Syntax_node3(v___x_738_, v___x_739_, v___x_735_, v___x_741_, v___x_736_);
v___x_743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_743_, 0, v___x_742_);
lean_ctor_set(v___x_743_, 1, v_a_722_);
return v___x_743_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______8___boxed(lean_object* v_x_744_, lean_object* v_a_745_, lean_object* v_a_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______8(v_x_744_, v_a_745_, v_a_746_);
lean_dec_ref(v_a_745_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______9(lean_object* v_x_768_, lean_object* v_a_769_, lean_object* v_a_770_){
_start:
{
lean_object* v___x_771_; uint8_t v___x_772_; 
v___x_771_ = ((lean_object*)(l_Lean_termSatisfies__binder__pred_x25_____00__closed__1));
lean_inc(v_x_768_);
v___x_772_ = l_Lean_Syntax_isOfKind(v_x_768_, v___x_771_);
if (v___x_772_ == 0)
{
lean_object* v___x_773_; lean_object* v___x_774_; 
lean_dec(v_x_768_);
v___x_773_ = lean_box(1);
v___x_774_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_774_, 0, v___x_773_);
lean_ctor_set(v___x_774_, 1, v_a_770_);
return v___x_774_;
}
else
{
lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; uint8_t v___x_778_; 
v___x_775_ = lean_unsigned_to_nat(2u);
v___x_776_ = l_Lean_Syntax_getArg(v_x_768_, v___x_775_);
v___x_777_ = ((lean_object*)(l_Lean_binderPred_u2282___00__closed__1));
lean_inc(v___x_776_);
v___x_778_ = l_Lean_Syntax_isOfKind(v___x_776_, v___x_777_);
if (v___x_778_ == 0)
{
lean_object* v___x_779_; lean_object* v___x_780_; 
lean_dec(v___x_776_);
lean_dec(v_x_768_);
v___x_779_ = lean_box(1);
v___x_780_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_780_, 0, v___x_779_);
lean_ctor_set(v___x_780_, 1, v_a_770_);
return v___x_780_;
}
else
{
lean_object* v_ref_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; uint8_t v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; 
v_ref_781_ = lean_ctor_get(v_a_769_, 5);
v___x_782_ = lean_unsigned_to_nat(1u);
v___x_783_ = l_Lean_Syntax_getArg(v_x_768_, v___x_782_);
lean_dec(v_x_768_);
v___x_784_ = l_Lean_Syntax_getArg(v___x_776_, v___x_782_);
lean_dec(v___x_776_);
v___x_785_ = 0;
v___x_786_ = l_Lean_SourceInfo_fromRef(v_ref_781_, v___x_785_);
v___x_787_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______9___closed__1));
v___x_788_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______9___closed__2));
lean_inc(v___x_786_);
v___x_789_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_789_, 0, v___x_786_);
lean_ctor_set(v___x_789_, 1, v___x_788_);
v___x_790_ = l_Lean_Syntax_node3(v___x_786_, v___x_787_, v___x_783_, v___x_789_, v___x_784_);
v___x_791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_791_, 0, v___x_790_);
lean_ctor_set(v___x_791_, 1, v_a_770_);
return v___x_791_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______9___boxed(lean_object* v_x_792_, lean_object* v_a_793_, lean_object* v_a_794_){
_start:
{
lean_object* v_res_795_; 
v_res_795_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______9(v_x_792_, v_a_793_, v_a_794_);
lean_dec_ref(v_a_793_);
return v_res_795_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______10(lean_object* v_x_816_, lean_object* v_a_817_, lean_object* v_a_818_){
_start:
{
lean_object* v___x_819_; uint8_t v___x_820_; 
v___x_819_ = ((lean_object*)(l_Lean_termSatisfies__binder__pred_x25_____00__closed__1));
lean_inc(v_x_816_);
v___x_820_ = l_Lean_Syntax_isOfKind(v_x_816_, v___x_819_);
if (v___x_820_ == 0)
{
lean_object* v___x_821_; lean_object* v___x_822_; 
lean_dec(v_x_816_);
v___x_821_ = lean_box(1);
v___x_822_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_822_, 0, v___x_821_);
lean_ctor_set(v___x_822_, 1, v_a_818_);
return v___x_822_;
}
else
{
lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; uint8_t v___x_826_; 
v___x_823_ = lean_unsigned_to_nat(2u);
v___x_824_ = l_Lean_Syntax_getArg(v_x_816_, v___x_823_);
v___x_825_ = ((lean_object*)(l_Lean_binderPred_u2287___00__closed__1));
lean_inc(v___x_824_);
v___x_826_ = l_Lean_Syntax_isOfKind(v___x_824_, v___x_825_);
if (v___x_826_ == 0)
{
lean_object* v___x_827_; lean_object* v___x_828_; 
lean_dec(v___x_824_);
lean_dec(v_x_816_);
v___x_827_ = lean_box(1);
v___x_828_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_828_, 0, v___x_827_);
lean_ctor_set(v___x_828_, 1, v_a_818_);
return v___x_828_;
}
else
{
lean_object* v_ref_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; uint8_t v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
v_ref_829_ = lean_ctor_get(v_a_817_, 5);
v___x_830_ = lean_unsigned_to_nat(1u);
v___x_831_ = l_Lean_Syntax_getArg(v_x_816_, v___x_830_);
lean_dec(v_x_816_);
v___x_832_ = l_Lean_Syntax_getArg(v___x_824_, v___x_830_);
lean_dec(v___x_824_);
v___x_833_ = 0;
v___x_834_ = l_Lean_SourceInfo_fromRef(v_ref_829_, v___x_833_);
v___x_835_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______10___closed__1));
v___x_836_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______10___closed__2));
lean_inc(v___x_834_);
v___x_837_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_837_, 0, v___x_834_);
lean_ctor_set(v___x_837_, 1, v___x_836_);
v___x_838_ = l_Lean_Syntax_node3(v___x_834_, v___x_835_, v___x_831_, v___x_837_, v___x_832_);
v___x_839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_839_, 0, v___x_838_);
lean_ctor_set(v___x_839_, 1, v_a_818_);
return v___x_839_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______10___boxed(lean_object* v_x_840_, lean_object* v_a_841_, lean_object* v_a_842_){
_start:
{
lean_object* v_res_843_; 
v_res_843_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______10(v_x_840_, v_a_841_, v_a_842_);
lean_dec_ref(v_a_841_);
return v_res_843_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______11(lean_object* v_x_864_, lean_object* v_a_865_, lean_object* v_a_866_){
_start:
{
lean_object* v___x_867_; uint8_t v___x_868_; 
v___x_867_ = ((lean_object*)(l_Lean_termSatisfies__binder__pred_x25_____00__closed__1));
lean_inc(v_x_864_);
v___x_868_ = l_Lean_Syntax_isOfKind(v_x_864_, v___x_867_);
if (v___x_868_ == 0)
{
lean_object* v___x_869_; lean_object* v___x_870_; 
lean_dec(v_x_864_);
v___x_869_ = lean_box(1);
v___x_870_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_870_, 0, v___x_869_);
lean_ctor_set(v___x_870_, 1, v_a_866_);
return v___x_870_;
}
else
{
lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; uint8_t v___x_874_; 
v___x_871_ = lean_unsigned_to_nat(2u);
v___x_872_ = l_Lean_Syntax_getArg(v_x_864_, v___x_871_);
v___x_873_ = ((lean_object*)(l_Lean_binderPred_u2283___00__closed__1));
lean_inc(v___x_872_);
v___x_874_ = l_Lean_Syntax_isOfKind(v___x_872_, v___x_873_);
if (v___x_874_ == 0)
{
lean_object* v___x_875_; lean_object* v___x_876_; 
lean_dec(v___x_872_);
lean_dec(v_x_864_);
v___x_875_ = lean_box(1);
v___x_876_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_876_, 0, v___x_875_);
lean_ctor_set(v___x_876_, 1, v_a_866_);
return v___x_876_;
}
else
{
lean_object* v_ref_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; uint8_t v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; 
v_ref_877_ = lean_ctor_get(v_a_865_, 5);
v___x_878_ = lean_unsigned_to_nat(1u);
v___x_879_ = l_Lean_Syntax_getArg(v_x_864_, v___x_878_);
lean_dec(v_x_864_);
v___x_880_ = l_Lean_Syntax_getArg(v___x_872_, v___x_878_);
lean_dec(v___x_872_);
v___x_881_ = 0;
v___x_882_ = l_Lean_SourceInfo_fromRef(v_ref_877_, v___x_881_);
v___x_883_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______11___closed__1));
v___x_884_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______11___closed__2));
lean_inc(v___x_882_);
v___x_885_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_885_, 0, v___x_882_);
lean_ctor_set(v___x_885_, 1, v___x_884_);
v___x_886_ = l_Lean_Syntax_node3(v___x_882_, v___x_883_, v___x_879_, v___x_885_, v___x_880_);
v___x_887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_887_, 0, v___x_886_);
lean_ctor_set(v___x_887_, 1, v_a_866_);
return v___x_887_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______11___boxed(lean_object* v_x_888_, lean_object* v_a_889_, lean_object* v_a_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______11(v_x_888_, v_a_889_, v_a_890_);
lean_dec_ref(v_a_889_);
return v_res_891_;
}
}
lean_object* runtime_initialize_Init_Notation(uint8_t builtin);
lean_object* runtime_initialize_Init_Meta_Defs(uint8_t builtin);
lean_object* runtime_initialize_Init_NotationExtra(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_BinderPredicates(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Notation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Meta_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_NotationExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Init_Grind_Tactics(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_BinderPredicates(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Init_Grind_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Category_binderPred = _init_l_Lean_Parser_Category_binderPred();
lean_mark_persistent(l_Lean_Parser_Category_binderPred);
l_Lean_term_u2203_____x2c__ = _init_l_Lean_term_u2203_____x2c__();
lean_mark_persistent(l_Lean_term_u2203_____x2c__);
l_Lean_term_u2200_____x2c__ = _init_l_Lean_term_u2200_____x2c__();
lean_mark_persistent(l_Lean_term_u2200_____x2c__);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Grind_Tactics(uint8_t builtin);
lean_object* initialize_Init_Notation(uint8_t builtin);
lean_object* initialize_Init_Meta_Defs(uint8_t builtin);
lean_object* initialize_Init_NotationExtra(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_BinderPredicates(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Notation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Meta_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_NotationExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_BinderPredicates(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_BinderPredicates(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_BinderPredicates(builtin);
}
#ifdef __cplusplus
}
#endif

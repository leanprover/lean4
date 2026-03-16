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
lean_dec_ref(v_a_175_);
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
lean_dec_ref(v_a_175_);
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
lean_dec_ref(v_a_175_);
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
lean_inc(v_quotContext_195_);
v_currMacroScope_196_ = lean_ctor_get(v_a_175_, 2);
lean_inc(v_currMacroScope_196_);
v_ref_197_ = lean_ctor_get(v_a_175_, 5);
lean_inc(v_ref_197_);
lean_dec_ref(v_a_175_);
v___x_198_ = lean_unsigned_to_nat(2u);
v___x_199_ = l_Lean_Syntax_getArg(v_x_174_, v___x_198_);
v___x_200_ = lean_unsigned_to_nat(4u);
v___x_201_ = l_Lean_Syntax_getArg(v_x_174_, v___x_200_);
lean_dec(v_x_174_);
v___x_202_ = l_Lean_SourceInfo_fromRef(v_ref_197_, v___x_190_);
lean_dec(v_ref_197_);
v___x_203_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__7));
v___x_204_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__8));
lean_inc(v___x_202_);
v___x_205_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_205_, 0, v___x_202_);
lean_ctor_set(v___x_205_, 1, v___x_204_);
v___x_206_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__10));
v___x_207_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__12));
v___x_208_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__14));
v___x_209_ = lean_obj_once(&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__16, &l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__16_once, _init_l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__16);
v___x_210_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__17));
v___x_211_ = l_Lean_addMacroScope(v_quotContext_195_, v___x_210_, v_currMacroScope_196_);
v___x_212_ = lean_box(0);
lean_inc(v___x_202_);
v___x_213_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_213_, 0, v___x_202_);
lean_ctor_set(v___x_213_, 1, v___x_209_);
lean_ctor_set(v___x_213_, 2, v___x_211_);
lean_ctor_set(v___x_213_, 3, v___x_212_);
lean_inc_ref(v___x_213_);
lean_inc(v___x_202_);
v___x_214_ = l_Lean_Syntax_node1(v___x_202_, v___x_183_, v___x_213_);
lean_inc(v___x_202_);
v___x_215_ = l_Lean_Syntax_node1(v___x_202_, v___x_208_, v___x_214_);
v___x_216_ = lean_obj_once(&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__18, &l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__18_once, _init_l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__18);
lean_inc(v___x_202_);
v___x_217_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_217_, 0, v___x_202_);
lean_ctor_set(v___x_217_, 1, v___x_208_);
lean_ctor_set(v___x_217_, 2, v___x_216_);
lean_inc(v___x_202_);
v___x_218_ = l_Lean_Syntax_node2(v___x_202_, v___x_207_, v___x_215_, v___x_217_);
lean_inc(v___x_202_);
v___x_219_ = l_Lean_Syntax_node1(v___x_202_, v___x_206_, v___x_218_);
v___x_220_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__19));
lean_inc(v___x_202_);
v___x_221_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_221_, 0, v___x_202_);
lean_ctor_set(v___x_221_, 1, v___x_220_);
v___x_222_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__21));
v___x_223_ = ((lean_object*)(l_Lean_termSatisfies__binder__pred_x25_____00__closed__1));
v___x_224_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__22));
lean_inc(v___x_202_);
v___x_225_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_225_, 0, v___x_202_);
lean_ctor_set(v___x_225_, 1, v___x_224_);
lean_inc(v___x_202_);
v___x_226_ = l_Lean_Syntax_node3(v___x_202_, v___x_223_, v___x_225_, v___x_213_, v___x_199_);
v___x_227_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__23));
lean_inc(v___x_202_);
v___x_228_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_228_, 0, v___x_202_);
lean_ctor_set(v___x_228_, 1, v___x_227_);
lean_inc(v___x_202_);
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
lean_inc(v_ref_232_);
lean_dec_ref(v_a_175_);
v___x_233_ = lean_unsigned_to_nat(2u);
v___x_234_ = l_Lean_Syntax_getArg(v_x_174_, v___x_233_);
v___x_235_ = lean_unsigned_to_nat(4u);
v___x_236_ = l_Lean_Syntax_getArg(v_x_174_, v___x_235_);
lean_dec(v_x_174_);
v___x_237_ = 0;
v___x_238_ = l_Lean_SourceInfo_fromRef(v_ref_232_, v___x_237_);
lean_dec(v_ref_232_);
v___x_239_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__7));
v___x_240_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__8));
lean_inc(v___x_238_);
v___x_241_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_241_, 0, v___x_238_);
lean_ctor_set(v___x_241_, 1, v___x_240_);
v___x_242_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__10));
v___x_243_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__12));
v___x_244_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__14));
lean_inc(v___x_188_);
lean_inc(v___x_238_);
v___x_245_ = l_Lean_Syntax_node1(v___x_238_, v___x_183_, v___x_188_);
lean_inc(v___x_238_);
v___x_246_ = l_Lean_Syntax_node1(v___x_238_, v___x_244_, v___x_245_);
v___x_247_ = lean_obj_once(&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__18, &l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__18_once, _init_l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__18);
lean_inc(v___x_238_);
v___x_248_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_248_, 0, v___x_238_);
lean_ctor_set(v___x_248_, 1, v___x_244_);
lean_ctor_set(v___x_248_, 2, v___x_247_);
lean_inc(v___x_238_);
v___x_249_ = l_Lean_Syntax_node2(v___x_238_, v___x_243_, v___x_246_, v___x_248_);
lean_inc(v___x_238_);
v___x_250_ = l_Lean_Syntax_node1(v___x_238_, v___x_242_, v___x_249_);
v___x_251_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__19));
lean_inc(v___x_238_);
v___x_252_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_252_, 0, v___x_238_);
lean_ctor_set(v___x_252_, 1, v___x_251_);
v___x_253_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__21));
v___x_254_ = ((lean_object*)(l_Lean_termSatisfies__binder__pred_x25_____00__closed__1));
v___x_255_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__22));
lean_inc(v___x_238_);
v___x_256_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_256_, 0, v___x_238_);
lean_ctor_set(v___x_256_, 1, v___x_255_);
lean_inc(v___x_238_);
v___x_257_ = l_Lean_Syntax_node3(v___x_238_, v___x_254_, v___x_256_, v___x_188_, v___x_234_);
v___x_258_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__23));
lean_inc(v___x_238_);
v___x_259_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_259_, 0, v___x_238_);
lean_ctor_set(v___x_259_, 1, v___x_258_);
lean_inc(v___x_238_);
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
LEAN_EXPORT lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1(lean_object* v_x_277_, lean_object* v_a_278_, lean_object* v_a_279_){
_start:
{
lean_object* v___x_280_; uint8_t v___x_281_; 
v___x_280_ = ((lean_object*)(l_Lean_term_u2200_____x2c___00__closed__1));
lean_inc(v_x_277_);
v___x_281_ = l_Lean_Syntax_isOfKind(v_x_277_, v___x_280_);
if (v___x_281_ == 0)
{
lean_object* v___x_282_; lean_object* v___x_283_; 
lean_dec_ref(v_a_278_);
lean_dec(v_x_277_);
v___x_282_ = lean_box(1);
v___x_283_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_283_, 0, v___x_282_);
lean_ctor_set(v___x_283_, 1, v_a_279_);
return v___x_283_;
}
else
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; uint8_t v___x_287_; 
v___x_284_ = lean_unsigned_to_nat(1u);
v___x_285_ = l_Lean_Syntax_getArg(v_x_277_, v___x_284_);
v___x_286_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__1));
lean_inc(v___x_285_);
v___x_287_ = l_Lean_Syntax_isOfKind(v___x_285_, v___x_286_);
if (v___x_287_ == 0)
{
lean_object* v___x_288_; lean_object* v___x_289_; 
lean_dec(v___x_285_);
lean_dec_ref(v_a_278_);
lean_dec(v_x_277_);
v___x_288_ = lean_box(1);
v___x_289_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_289_, 0, v___x_288_);
lean_ctor_set(v___x_289_, 1, v_a_279_);
return v___x_289_;
}
else
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; uint8_t v___x_293_; 
v___x_290_ = lean_unsigned_to_nat(0u);
v___x_291_ = l_Lean_Syntax_getArg(v___x_285_, v___x_290_);
lean_dec(v___x_285_);
v___x_292_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__3));
lean_inc(v___x_291_);
v___x_293_ = l_Lean_Syntax_isOfKind(v___x_291_, v___x_292_);
if (v___x_293_ == 0)
{
lean_object* v___x_294_; uint8_t v___x_295_; 
v___x_294_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__5));
v___x_295_ = l_Lean_Syntax_isOfKind(v___x_291_, v___x_294_);
if (v___x_295_ == 0)
{
lean_object* v___x_296_; lean_object* v___x_297_; 
lean_dec_ref(v_a_278_);
lean_dec(v_x_277_);
v___x_296_ = lean_box(1);
v___x_297_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_297_, 0, v___x_296_);
lean_ctor_set(v___x_297_, 1, v_a_279_);
return v___x_297_;
}
else
{
lean_object* v_quotContext_298_; lean_object* v_currMacroScope_299_; lean_object* v_ref_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
v_quotContext_298_ = lean_ctor_get(v_a_278_, 1);
lean_inc(v_quotContext_298_);
v_currMacroScope_299_ = lean_ctor_get(v_a_278_, 2);
lean_inc(v_currMacroScope_299_);
v_ref_300_ = lean_ctor_get(v_a_278_, 5);
lean_inc(v_ref_300_);
lean_dec_ref(v_a_278_);
v___x_301_ = lean_unsigned_to_nat(2u);
v___x_302_ = l_Lean_Syntax_getArg(v_x_277_, v___x_301_);
v___x_303_ = lean_unsigned_to_nat(4u);
v___x_304_ = l_Lean_Syntax_getArg(v_x_277_, v___x_303_);
lean_dec(v_x_277_);
v___x_305_ = l_Lean_SourceInfo_fromRef(v_ref_300_, v___x_293_);
lean_dec(v_ref_300_);
v___x_306_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__1));
v___x_307_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__2));
lean_inc(v___x_305_);
v___x_308_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_308_, 0, v___x_305_);
lean_ctor_set(v___x_308_, 1, v___x_307_);
v___x_309_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__14));
v___x_310_ = lean_obj_once(&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__16, &l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__16_once, _init_l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__16);
v___x_311_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__17));
v___x_312_ = l_Lean_addMacroScope(v_quotContext_298_, v___x_311_, v_currMacroScope_299_);
v___x_313_ = lean_box(0);
lean_inc(v___x_305_);
v___x_314_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_314_, 0, v___x_305_);
lean_ctor_set(v___x_314_, 1, v___x_310_);
lean_ctor_set(v___x_314_, 2, v___x_312_);
lean_ctor_set(v___x_314_, 3, v___x_313_);
lean_inc_ref(v___x_314_);
lean_inc(v___x_305_);
v___x_315_ = l_Lean_Syntax_node1(v___x_305_, v___x_309_, v___x_314_);
v___x_316_ = lean_obj_once(&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__18, &l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__18_once, _init_l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__18);
lean_inc(v___x_305_);
v___x_317_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_317_, 0, v___x_305_);
lean_ctor_set(v___x_317_, 1, v___x_309_);
lean_ctor_set(v___x_317_, 2, v___x_316_);
v___x_318_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__19));
lean_inc(v___x_305_);
v___x_319_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_319_, 0, v___x_305_);
lean_ctor_set(v___x_319_, 1, v___x_318_);
v___x_320_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__4));
v___x_321_ = ((lean_object*)(l_Lean_termSatisfies__binder__pred_x25_____00__closed__1));
v___x_322_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__22));
lean_inc(v___x_305_);
v___x_323_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_323_, 0, v___x_305_);
lean_ctor_set(v___x_323_, 1, v___x_322_);
lean_inc(v___x_305_);
v___x_324_ = l_Lean_Syntax_node3(v___x_305_, v___x_321_, v___x_323_, v___x_314_, v___x_302_);
v___x_325_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__5));
lean_inc(v___x_305_);
v___x_326_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_326_, 0, v___x_305_);
lean_ctor_set(v___x_326_, 1, v___x_325_);
lean_inc(v___x_305_);
v___x_327_ = l_Lean_Syntax_node3(v___x_305_, v___x_320_, v___x_324_, v___x_326_, v___x_304_);
v___x_328_ = l_Lean_Syntax_node5(v___x_305_, v___x_306_, v___x_308_, v___x_315_, v___x_317_, v___x_319_, v___x_327_);
v___x_329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_329_, 0, v___x_328_);
lean_ctor_set(v___x_329_, 1, v_a_279_);
return v___x_329_;
}
}
else
{
lean_object* v_ref_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; uint8_t v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
v_ref_330_ = lean_ctor_get(v_a_278_, 5);
lean_inc(v_ref_330_);
lean_dec_ref(v_a_278_);
v___x_331_ = lean_unsigned_to_nat(2u);
v___x_332_ = l_Lean_Syntax_getArg(v_x_277_, v___x_331_);
v___x_333_ = lean_unsigned_to_nat(4u);
v___x_334_ = l_Lean_Syntax_getArg(v_x_277_, v___x_333_);
lean_dec(v_x_277_);
v___x_335_ = 0;
v___x_336_ = l_Lean_SourceInfo_fromRef(v_ref_330_, v___x_335_);
lean_dec(v_ref_330_);
v___x_337_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__1));
v___x_338_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__2));
lean_inc(v___x_336_);
v___x_339_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_339_, 0, v___x_336_);
lean_ctor_set(v___x_339_, 1, v___x_338_);
v___x_340_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__14));
lean_inc(v___x_291_);
lean_inc(v___x_336_);
v___x_341_ = l_Lean_Syntax_node1(v___x_336_, v___x_340_, v___x_291_);
v___x_342_ = lean_obj_once(&l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__18, &l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__18_once, _init_l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__18);
lean_inc(v___x_336_);
v___x_343_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_343_, 0, v___x_336_);
lean_ctor_set(v___x_343_, 1, v___x_340_);
lean_ctor_set(v___x_343_, 2, v___x_342_);
v___x_344_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__19));
lean_inc(v___x_336_);
v___x_345_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_345_, 0, v___x_336_);
lean_ctor_set(v___x_345_, 1, v___x_344_);
v___x_346_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__4));
v___x_347_ = ((lean_object*)(l_Lean_termSatisfies__binder__pred_x25_____00__closed__1));
v___x_348_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__22));
lean_inc(v___x_336_);
v___x_349_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_349_, 0, v___x_336_);
lean_ctor_set(v___x_349_, 1, v___x_348_);
lean_inc(v___x_336_);
v___x_350_ = l_Lean_Syntax_node3(v___x_336_, v___x_347_, v___x_349_, v___x_291_, v___x_332_);
v___x_351_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__5));
lean_inc(v___x_336_);
v___x_352_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_352_, 0, v___x_336_);
lean_ctor_set(v___x_352_, 1, v___x_351_);
lean_inc(v___x_336_);
v___x_353_ = l_Lean_Syntax_node3(v___x_336_, v___x_346_, v___x_350_, v___x_352_, v___x_334_);
v___x_354_ = l_Lean_Syntax_node5(v___x_336_, v___x_337_, v___x_339_, v___x_341_, v___x_343_, v___x_345_, v___x_353_);
v___x_355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_355_, 0, v___x_354_);
lean_ctor_set(v___x_355_, 1, v_a_279_);
return v___x_355_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______1(lean_object* v_x_376_, lean_object* v_a_377_, lean_object* v_a_378_){
_start:
{
lean_object* v___x_379_; uint8_t v___x_380_; 
v___x_379_ = ((lean_object*)(l_Lean_termSatisfies__binder__pred_x25_____00__closed__1));
lean_inc(v_x_376_);
v___x_380_ = l_Lean_Syntax_isOfKind(v_x_376_, v___x_379_);
if (v___x_380_ == 0)
{
lean_object* v___x_381_; lean_object* v___x_382_; 
lean_dec(v_x_376_);
v___x_381_ = lean_box(1);
v___x_382_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_382_, 0, v___x_381_);
lean_ctor_set(v___x_382_, 1, v_a_378_);
return v___x_382_;
}
else
{
lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; uint8_t v___x_386_; 
v___x_383_ = lean_unsigned_to_nat(2u);
v___x_384_ = l_Lean_Syntax_getArg(v_x_376_, v___x_383_);
v___x_385_ = ((lean_object*)(l_Lean_binderPred_x3e___00__closed__1));
lean_inc(v___x_384_);
v___x_386_ = l_Lean_Syntax_isOfKind(v___x_384_, v___x_385_);
if (v___x_386_ == 0)
{
lean_object* v___x_387_; lean_object* v___x_388_; 
lean_dec(v___x_384_);
lean_dec(v_x_376_);
v___x_387_ = lean_box(1);
v___x_388_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_388_, 0, v___x_387_);
lean_ctor_set(v___x_388_, 1, v_a_378_);
return v___x_388_;
}
else
{
lean_object* v_ref_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; uint8_t v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
v_ref_389_ = lean_ctor_get(v_a_377_, 5);
v___x_390_ = lean_unsigned_to_nat(1u);
v___x_391_ = l_Lean_Syntax_getArg(v_x_376_, v___x_390_);
lean_dec(v_x_376_);
v___x_392_ = l_Lean_Syntax_getArg(v___x_384_, v___x_390_);
lean_dec(v___x_384_);
v___x_393_ = 0;
v___x_394_ = l_Lean_SourceInfo_fromRef(v_ref_389_, v___x_393_);
v___x_395_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______1___closed__1));
v___x_396_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______1___closed__2));
lean_inc(v___x_394_);
v___x_397_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_397_, 0, v___x_394_);
lean_ctor_set(v___x_397_, 1, v___x_396_);
v___x_398_ = l_Lean_Syntax_node3(v___x_394_, v___x_395_, v___x_391_, v___x_397_, v___x_392_);
v___x_399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_399_, 0, v___x_398_);
lean_ctor_set(v___x_399_, 1, v_a_378_);
return v___x_399_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______1___boxed(lean_object* v_x_400_, lean_object* v_a_401_, lean_object* v_a_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______1(v_x_400_, v_a_401_, v_a_402_);
lean_dec_ref(v_a_401_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______2(lean_object* v_x_424_, lean_object* v_a_425_, lean_object* v_a_426_){
_start:
{
lean_object* v___x_427_; uint8_t v___x_428_; 
v___x_427_ = ((lean_object*)(l_Lean_termSatisfies__binder__pred_x25_____00__closed__1));
lean_inc(v_x_424_);
v___x_428_ = l_Lean_Syntax_isOfKind(v_x_424_, v___x_427_);
if (v___x_428_ == 0)
{
lean_object* v___x_429_; lean_object* v___x_430_; 
lean_dec(v_x_424_);
v___x_429_ = lean_box(1);
v___x_430_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_430_, 0, v___x_429_);
lean_ctor_set(v___x_430_, 1, v_a_426_);
return v___x_430_;
}
else
{
lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; uint8_t v___x_434_; 
v___x_431_ = lean_unsigned_to_nat(2u);
v___x_432_ = l_Lean_Syntax_getArg(v_x_424_, v___x_431_);
v___x_433_ = ((lean_object*)(l_Lean_binderPred_u2265___00__closed__1));
lean_inc(v___x_432_);
v___x_434_ = l_Lean_Syntax_isOfKind(v___x_432_, v___x_433_);
if (v___x_434_ == 0)
{
lean_object* v___x_435_; lean_object* v___x_436_; 
lean_dec(v___x_432_);
lean_dec(v_x_424_);
v___x_435_ = lean_box(1);
v___x_436_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_436_, 0, v___x_435_);
lean_ctor_set(v___x_436_, 1, v_a_426_);
return v___x_436_;
}
else
{
lean_object* v_ref_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; uint8_t v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; 
v_ref_437_ = lean_ctor_get(v_a_425_, 5);
v___x_438_ = lean_unsigned_to_nat(1u);
v___x_439_ = l_Lean_Syntax_getArg(v_x_424_, v___x_438_);
lean_dec(v_x_424_);
v___x_440_ = l_Lean_Syntax_getArg(v___x_432_, v___x_438_);
lean_dec(v___x_432_);
v___x_441_ = 0;
v___x_442_ = l_Lean_SourceInfo_fromRef(v_ref_437_, v___x_441_);
v___x_443_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______2___closed__1));
v___x_444_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______2___closed__2));
lean_inc(v___x_442_);
v___x_445_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_445_, 0, v___x_442_);
lean_ctor_set(v___x_445_, 1, v___x_444_);
v___x_446_ = l_Lean_Syntax_node3(v___x_442_, v___x_443_, v___x_439_, v___x_445_, v___x_440_);
v___x_447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_447_, 0, v___x_446_);
lean_ctor_set(v___x_447_, 1, v_a_426_);
return v___x_447_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______2___boxed(lean_object* v_x_448_, lean_object* v_a_449_, lean_object* v_a_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______2(v_x_448_, v_a_449_, v_a_450_);
lean_dec_ref(v_a_449_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______3(lean_object* v_x_472_, lean_object* v_a_473_, lean_object* v_a_474_){
_start:
{
lean_object* v___x_475_; uint8_t v___x_476_; 
v___x_475_ = ((lean_object*)(l_Lean_termSatisfies__binder__pred_x25_____00__closed__1));
lean_inc(v_x_472_);
v___x_476_ = l_Lean_Syntax_isOfKind(v_x_472_, v___x_475_);
if (v___x_476_ == 0)
{
lean_object* v___x_477_; lean_object* v___x_478_; 
lean_dec(v_x_472_);
v___x_477_ = lean_box(1);
v___x_478_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_478_, 0, v___x_477_);
lean_ctor_set(v___x_478_, 1, v_a_474_);
return v___x_478_;
}
else
{
lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; uint8_t v___x_482_; 
v___x_479_ = lean_unsigned_to_nat(2u);
v___x_480_ = l_Lean_Syntax_getArg(v_x_472_, v___x_479_);
v___x_481_ = ((lean_object*)(l_Lean_binderPred_x3c___00__closed__1));
lean_inc(v___x_480_);
v___x_482_ = l_Lean_Syntax_isOfKind(v___x_480_, v___x_481_);
if (v___x_482_ == 0)
{
lean_object* v___x_483_; lean_object* v___x_484_; 
lean_dec(v___x_480_);
lean_dec(v_x_472_);
v___x_483_ = lean_box(1);
v___x_484_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_484_, 0, v___x_483_);
lean_ctor_set(v___x_484_, 1, v_a_474_);
return v___x_484_;
}
else
{
lean_object* v_ref_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; uint8_t v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v_ref_485_ = lean_ctor_get(v_a_473_, 5);
v___x_486_ = lean_unsigned_to_nat(1u);
v___x_487_ = l_Lean_Syntax_getArg(v_x_472_, v___x_486_);
lean_dec(v_x_472_);
v___x_488_ = l_Lean_Syntax_getArg(v___x_480_, v___x_486_);
lean_dec(v___x_480_);
v___x_489_ = 0;
v___x_490_ = l_Lean_SourceInfo_fromRef(v_ref_485_, v___x_489_);
v___x_491_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______3___closed__1));
v___x_492_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______3___closed__2));
lean_inc(v___x_490_);
v___x_493_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_493_, 0, v___x_490_);
lean_ctor_set(v___x_493_, 1, v___x_492_);
v___x_494_ = l_Lean_Syntax_node3(v___x_490_, v___x_491_, v___x_487_, v___x_493_, v___x_488_);
v___x_495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_495_, 0, v___x_494_);
lean_ctor_set(v___x_495_, 1, v_a_474_);
return v___x_495_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______3___boxed(lean_object* v_x_496_, lean_object* v_a_497_, lean_object* v_a_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______3(v_x_496_, v_a_497_, v_a_498_);
lean_dec_ref(v_a_497_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______4(lean_object* v_x_520_, lean_object* v_a_521_, lean_object* v_a_522_){
_start:
{
lean_object* v___x_523_; uint8_t v___x_524_; 
v___x_523_ = ((lean_object*)(l_Lean_termSatisfies__binder__pred_x25_____00__closed__1));
lean_inc(v_x_520_);
v___x_524_ = l_Lean_Syntax_isOfKind(v_x_520_, v___x_523_);
if (v___x_524_ == 0)
{
lean_object* v___x_525_; lean_object* v___x_526_; 
lean_dec(v_x_520_);
v___x_525_ = lean_box(1);
v___x_526_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_526_, 0, v___x_525_);
lean_ctor_set(v___x_526_, 1, v_a_522_);
return v___x_526_;
}
else
{
lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; uint8_t v___x_530_; 
v___x_527_ = lean_unsigned_to_nat(2u);
v___x_528_ = l_Lean_Syntax_getArg(v_x_520_, v___x_527_);
v___x_529_ = ((lean_object*)(l_Lean_binderPred_u2264___00__closed__1));
lean_inc(v___x_528_);
v___x_530_ = l_Lean_Syntax_isOfKind(v___x_528_, v___x_529_);
if (v___x_530_ == 0)
{
lean_object* v___x_531_; lean_object* v___x_532_; 
lean_dec(v___x_528_);
lean_dec(v_x_520_);
v___x_531_ = lean_box(1);
v___x_532_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_532_, 0, v___x_531_);
lean_ctor_set(v___x_532_, 1, v_a_522_);
return v___x_532_;
}
else
{
lean_object* v_ref_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; uint8_t v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; 
v_ref_533_ = lean_ctor_get(v_a_521_, 5);
v___x_534_ = lean_unsigned_to_nat(1u);
v___x_535_ = l_Lean_Syntax_getArg(v_x_520_, v___x_534_);
lean_dec(v_x_520_);
v___x_536_ = l_Lean_Syntax_getArg(v___x_528_, v___x_534_);
lean_dec(v___x_528_);
v___x_537_ = 0;
v___x_538_ = l_Lean_SourceInfo_fromRef(v_ref_533_, v___x_537_);
v___x_539_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______4___closed__1));
v___x_540_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______4___closed__2));
lean_inc(v___x_538_);
v___x_541_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_541_, 0, v___x_538_);
lean_ctor_set(v___x_541_, 1, v___x_540_);
v___x_542_ = l_Lean_Syntax_node3(v___x_538_, v___x_539_, v___x_535_, v___x_541_, v___x_536_);
v___x_543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_543_, 0, v___x_542_);
lean_ctor_set(v___x_543_, 1, v_a_522_);
return v___x_543_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______4___boxed(lean_object* v_x_544_, lean_object* v_a_545_, lean_object* v_a_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______4(v_x_544_, v_a_545_, v_a_546_);
lean_dec_ref(v_a_545_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______5(lean_object* v_x_568_, lean_object* v_a_569_, lean_object* v_a_570_){
_start:
{
lean_object* v___x_571_; uint8_t v___x_572_; 
v___x_571_ = ((lean_object*)(l_Lean_termSatisfies__binder__pred_x25_____00__closed__1));
lean_inc(v_x_568_);
v___x_572_ = l_Lean_Syntax_isOfKind(v_x_568_, v___x_571_);
if (v___x_572_ == 0)
{
lean_object* v___x_573_; lean_object* v___x_574_; 
lean_dec(v_x_568_);
v___x_573_ = lean_box(1);
v___x_574_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_574_, 0, v___x_573_);
lean_ctor_set(v___x_574_, 1, v_a_570_);
return v___x_574_;
}
else
{
lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; uint8_t v___x_578_; 
v___x_575_ = lean_unsigned_to_nat(2u);
v___x_576_ = l_Lean_Syntax_getArg(v_x_568_, v___x_575_);
v___x_577_ = ((lean_object*)(l_Lean_binderPred_u2260___00__closed__1));
lean_inc(v___x_576_);
v___x_578_ = l_Lean_Syntax_isOfKind(v___x_576_, v___x_577_);
if (v___x_578_ == 0)
{
lean_object* v___x_579_; lean_object* v___x_580_; 
lean_dec(v___x_576_);
lean_dec(v_x_568_);
v___x_579_ = lean_box(1);
v___x_580_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_580_, 0, v___x_579_);
lean_ctor_set(v___x_580_, 1, v_a_570_);
return v___x_580_;
}
else
{
lean_object* v_ref_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; uint8_t v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
v_ref_581_ = lean_ctor_get(v_a_569_, 5);
v___x_582_ = lean_unsigned_to_nat(1u);
v___x_583_ = l_Lean_Syntax_getArg(v_x_568_, v___x_582_);
lean_dec(v_x_568_);
v___x_584_ = l_Lean_Syntax_getArg(v___x_576_, v___x_582_);
lean_dec(v___x_576_);
v___x_585_ = 0;
v___x_586_ = l_Lean_SourceInfo_fromRef(v_ref_581_, v___x_585_);
v___x_587_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______5___closed__1));
v___x_588_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______5___closed__2));
lean_inc(v___x_586_);
v___x_589_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_589_, 0, v___x_586_);
lean_ctor_set(v___x_589_, 1, v___x_588_);
v___x_590_ = l_Lean_Syntax_node3(v___x_586_, v___x_587_, v___x_583_, v___x_589_, v___x_584_);
v___x_591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_591_, 0, v___x_590_);
lean_ctor_set(v___x_591_, 1, v_a_570_);
return v___x_591_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______5___boxed(lean_object* v_x_592_, lean_object* v_a_593_, lean_object* v_a_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______5(v_x_592_, v_a_593_, v_a_594_);
lean_dec_ref(v_a_593_);
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______6(lean_object* v_x_616_, lean_object* v_a_617_, lean_object* v_a_618_){
_start:
{
lean_object* v___x_619_; uint8_t v___x_620_; 
v___x_619_ = ((lean_object*)(l_Lean_termSatisfies__binder__pred_x25_____00__closed__1));
lean_inc(v_x_616_);
v___x_620_ = l_Lean_Syntax_isOfKind(v_x_616_, v___x_619_);
if (v___x_620_ == 0)
{
lean_object* v___x_621_; lean_object* v___x_622_; 
lean_dec(v_x_616_);
v___x_621_ = lean_box(1);
v___x_622_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_622_, 0, v___x_621_);
lean_ctor_set(v___x_622_, 1, v_a_618_);
return v___x_622_;
}
else
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; uint8_t v___x_626_; 
v___x_623_ = lean_unsigned_to_nat(2u);
v___x_624_ = l_Lean_Syntax_getArg(v_x_616_, v___x_623_);
v___x_625_ = ((lean_object*)(l_Lean_binderPred_u2208___00__closed__1));
lean_inc(v___x_624_);
v___x_626_ = l_Lean_Syntax_isOfKind(v___x_624_, v___x_625_);
if (v___x_626_ == 0)
{
lean_object* v___x_627_; lean_object* v___x_628_; 
lean_dec(v___x_624_);
lean_dec(v_x_616_);
v___x_627_ = lean_box(1);
v___x_628_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_628_, 0, v___x_627_);
lean_ctor_set(v___x_628_, 1, v_a_618_);
return v___x_628_;
}
else
{
lean_object* v_ref_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; uint8_t v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v_ref_629_ = lean_ctor_get(v_a_617_, 5);
v___x_630_ = lean_unsigned_to_nat(1u);
v___x_631_ = l_Lean_Syntax_getArg(v_x_616_, v___x_630_);
lean_dec(v_x_616_);
v___x_632_ = l_Lean_Syntax_getArg(v___x_624_, v___x_630_);
lean_dec(v___x_624_);
v___x_633_ = 0;
v___x_634_ = l_Lean_SourceInfo_fromRef(v_ref_629_, v___x_633_);
v___x_635_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______6___closed__1));
v___x_636_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______6___closed__2));
lean_inc(v___x_634_);
v___x_637_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_637_, 0, v___x_634_);
lean_ctor_set(v___x_637_, 1, v___x_636_);
v___x_638_ = l_Lean_Syntax_node3(v___x_634_, v___x_635_, v___x_631_, v___x_637_, v___x_632_);
v___x_639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_639_, 0, v___x_638_);
lean_ctor_set(v___x_639_, 1, v_a_618_);
return v___x_639_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______6___boxed(lean_object* v_x_640_, lean_object* v_a_641_, lean_object* v_a_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______6(v_x_640_, v_a_641_, v_a_642_);
lean_dec_ref(v_a_641_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______7(lean_object* v_x_664_, lean_object* v_a_665_, lean_object* v_a_666_){
_start:
{
lean_object* v___x_667_; uint8_t v___x_668_; 
v___x_667_ = ((lean_object*)(l_Lean_termSatisfies__binder__pred_x25_____00__closed__1));
lean_inc(v_x_664_);
v___x_668_ = l_Lean_Syntax_isOfKind(v_x_664_, v___x_667_);
if (v___x_668_ == 0)
{
lean_object* v___x_669_; lean_object* v___x_670_; 
lean_dec(v_x_664_);
v___x_669_ = lean_box(1);
v___x_670_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_670_, 0, v___x_669_);
lean_ctor_set(v___x_670_, 1, v_a_666_);
return v___x_670_;
}
else
{
lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; uint8_t v___x_674_; 
v___x_671_ = lean_unsigned_to_nat(2u);
v___x_672_ = l_Lean_Syntax_getArg(v_x_664_, v___x_671_);
v___x_673_ = ((lean_object*)(l_Lean_binderPred_u2209___00__closed__1));
lean_inc(v___x_672_);
v___x_674_ = l_Lean_Syntax_isOfKind(v___x_672_, v___x_673_);
if (v___x_674_ == 0)
{
lean_object* v___x_675_; lean_object* v___x_676_; 
lean_dec(v___x_672_);
lean_dec(v_x_664_);
v___x_675_ = lean_box(1);
v___x_676_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_676_, 0, v___x_675_);
lean_ctor_set(v___x_676_, 1, v_a_666_);
return v___x_676_;
}
else
{
lean_object* v_ref_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; uint8_t v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
v_ref_677_ = lean_ctor_get(v_a_665_, 5);
v___x_678_ = lean_unsigned_to_nat(1u);
v___x_679_ = l_Lean_Syntax_getArg(v_x_664_, v___x_678_);
lean_dec(v_x_664_);
v___x_680_ = l_Lean_Syntax_getArg(v___x_672_, v___x_678_);
lean_dec(v___x_672_);
v___x_681_ = 0;
v___x_682_ = l_Lean_SourceInfo_fromRef(v_ref_677_, v___x_681_);
v___x_683_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______7___closed__1));
v___x_684_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______7___closed__2));
lean_inc(v___x_682_);
v___x_685_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_685_, 0, v___x_682_);
lean_ctor_set(v___x_685_, 1, v___x_684_);
v___x_686_ = l_Lean_Syntax_node3(v___x_682_, v___x_683_, v___x_679_, v___x_685_, v___x_680_);
v___x_687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_687_, 0, v___x_686_);
lean_ctor_set(v___x_687_, 1, v_a_666_);
return v___x_687_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______7___boxed(lean_object* v_x_688_, lean_object* v_a_689_, lean_object* v_a_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______7(v_x_688_, v_a_689_, v_a_690_);
lean_dec_ref(v_a_689_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______8(lean_object* v_x_712_, lean_object* v_a_713_, lean_object* v_a_714_){
_start:
{
lean_object* v___x_715_; uint8_t v___x_716_; 
v___x_715_ = ((lean_object*)(l_Lean_termSatisfies__binder__pred_x25_____00__closed__1));
lean_inc(v_x_712_);
v___x_716_ = l_Lean_Syntax_isOfKind(v_x_712_, v___x_715_);
if (v___x_716_ == 0)
{
lean_object* v___x_717_; lean_object* v___x_718_; 
lean_dec(v_x_712_);
v___x_717_ = lean_box(1);
v___x_718_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_718_, 0, v___x_717_);
lean_ctor_set(v___x_718_, 1, v_a_714_);
return v___x_718_;
}
else
{
lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; uint8_t v___x_722_; 
v___x_719_ = lean_unsigned_to_nat(2u);
v___x_720_ = l_Lean_Syntax_getArg(v_x_712_, v___x_719_);
v___x_721_ = ((lean_object*)(l_Lean_binderPred_u2286___00__closed__1));
lean_inc(v___x_720_);
v___x_722_ = l_Lean_Syntax_isOfKind(v___x_720_, v___x_721_);
if (v___x_722_ == 0)
{
lean_object* v___x_723_; lean_object* v___x_724_; 
lean_dec(v___x_720_);
lean_dec(v_x_712_);
v___x_723_ = lean_box(1);
v___x_724_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_724_, 0, v___x_723_);
lean_ctor_set(v___x_724_, 1, v_a_714_);
return v___x_724_;
}
else
{
lean_object* v_ref_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; uint8_t v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; 
v_ref_725_ = lean_ctor_get(v_a_713_, 5);
v___x_726_ = lean_unsigned_to_nat(1u);
v___x_727_ = l_Lean_Syntax_getArg(v_x_712_, v___x_726_);
lean_dec(v_x_712_);
v___x_728_ = l_Lean_Syntax_getArg(v___x_720_, v___x_726_);
lean_dec(v___x_720_);
v___x_729_ = 0;
v___x_730_ = l_Lean_SourceInfo_fromRef(v_ref_725_, v___x_729_);
v___x_731_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______8___closed__1));
v___x_732_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______8___closed__2));
lean_inc(v___x_730_);
v___x_733_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_733_, 0, v___x_730_);
lean_ctor_set(v___x_733_, 1, v___x_732_);
v___x_734_ = l_Lean_Syntax_node3(v___x_730_, v___x_731_, v___x_727_, v___x_733_, v___x_728_);
v___x_735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_735_, 0, v___x_734_);
lean_ctor_set(v___x_735_, 1, v_a_714_);
return v___x_735_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______8___boxed(lean_object* v_x_736_, lean_object* v_a_737_, lean_object* v_a_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______8(v_x_736_, v_a_737_, v_a_738_);
lean_dec_ref(v_a_737_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______9(lean_object* v_x_760_, lean_object* v_a_761_, lean_object* v_a_762_){
_start:
{
lean_object* v___x_763_; uint8_t v___x_764_; 
v___x_763_ = ((lean_object*)(l_Lean_termSatisfies__binder__pred_x25_____00__closed__1));
lean_inc(v_x_760_);
v___x_764_ = l_Lean_Syntax_isOfKind(v_x_760_, v___x_763_);
if (v___x_764_ == 0)
{
lean_object* v___x_765_; lean_object* v___x_766_; 
lean_dec(v_x_760_);
v___x_765_ = lean_box(1);
v___x_766_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_766_, 0, v___x_765_);
lean_ctor_set(v___x_766_, 1, v_a_762_);
return v___x_766_;
}
else
{
lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; uint8_t v___x_770_; 
v___x_767_ = lean_unsigned_to_nat(2u);
v___x_768_ = l_Lean_Syntax_getArg(v_x_760_, v___x_767_);
v___x_769_ = ((lean_object*)(l_Lean_binderPred_u2282___00__closed__1));
lean_inc(v___x_768_);
v___x_770_ = l_Lean_Syntax_isOfKind(v___x_768_, v___x_769_);
if (v___x_770_ == 0)
{
lean_object* v___x_771_; lean_object* v___x_772_; 
lean_dec(v___x_768_);
lean_dec(v_x_760_);
v___x_771_ = lean_box(1);
v___x_772_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_772_, 0, v___x_771_);
lean_ctor_set(v___x_772_, 1, v_a_762_);
return v___x_772_;
}
else
{
lean_object* v_ref_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; uint8_t v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
v_ref_773_ = lean_ctor_get(v_a_761_, 5);
v___x_774_ = lean_unsigned_to_nat(1u);
v___x_775_ = l_Lean_Syntax_getArg(v_x_760_, v___x_774_);
lean_dec(v_x_760_);
v___x_776_ = l_Lean_Syntax_getArg(v___x_768_, v___x_774_);
lean_dec(v___x_768_);
v___x_777_ = 0;
v___x_778_ = l_Lean_SourceInfo_fromRef(v_ref_773_, v___x_777_);
v___x_779_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______9___closed__1));
v___x_780_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______9___closed__2));
lean_inc(v___x_778_);
v___x_781_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_781_, 0, v___x_778_);
lean_ctor_set(v___x_781_, 1, v___x_780_);
v___x_782_ = l_Lean_Syntax_node3(v___x_778_, v___x_779_, v___x_775_, v___x_781_, v___x_776_);
v___x_783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_783_, 0, v___x_782_);
lean_ctor_set(v___x_783_, 1, v_a_762_);
return v___x_783_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______9___boxed(lean_object* v_x_784_, lean_object* v_a_785_, lean_object* v_a_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______9(v_x_784_, v_a_785_, v_a_786_);
lean_dec_ref(v_a_785_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______10(lean_object* v_x_808_, lean_object* v_a_809_, lean_object* v_a_810_){
_start:
{
lean_object* v___x_811_; uint8_t v___x_812_; 
v___x_811_ = ((lean_object*)(l_Lean_termSatisfies__binder__pred_x25_____00__closed__1));
lean_inc(v_x_808_);
v___x_812_ = l_Lean_Syntax_isOfKind(v_x_808_, v___x_811_);
if (v___x_812_ == 0)
{
lean_object* v___x_813_; lean_object* v___x_814_; 
lean_dec(v_x_808_);
v___x_813_ = lean_box(1);
v___x_814_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_814_, 0, v___x_813_);
lean_ctor_set(v___x_814_, 1, v_a_810_);
return v___x_814_;
}
else
{
lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; uint8_t v___x_818_; 
v___x_815_ = lean_unsigned_to_nat(2u);
v___x_816_ = l_Lean_Syntax_getArg(v_x_808_, v___x_815_);
v___x_817_ = ((lean_object*)(l_Lean_binderPred_u2287___00__closed__1));
lean_inc(v___x_816_);
v___x_818_ = l_Lean_Syntax_isOfKind(v___x_816_, v___x_817_);
if (v___x_818_ == 0)
{
lean_object* v___x_819_; lean_object* v___x_820_; 
lean_dec(v___x_816_);
lean_dec(v_x_808_);
v___x_819_ = lean_box(1);
v___x_820_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_820_, 0, v___x_819_);
lean_ctor_set(v___x_820_, 1, v_a_810_);
return v___x_820_;
}
else
{
lean_object* v_ref_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; uint8_t v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
v_ref_821_ = lean_ctor_get(v_a_809_, 5);
v___x_822_ = lean_unsigned_to_nat(1u);
v___x_823_ = l_Lean_Syntax_getArg(v_x_808_, v___x_822_);
lean_dec(v_x_808_);
v___x_824_ = l_Lean_Syntax_getArg(v___x_816_, v___x_822_);
lean_dec(v___x_816_);
v___x_825_ = 0;
v___x_826_ = l_Lean_SourceInfo_fromRef(v_ref_821_, v___x_825_);
v___x_827_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______10___closed__1));
v___x_828_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______10___closed__2));
lean_inc(v___x_826_);
v___x_829_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_829_, 0, v___x_826_);
lean_ctor_set(v___x_829_, 1, v___x_828_);
v___x_830_ = l_Lean_Syntax_node3(v___x_826_, v___x_827_, v___x_823_, v___x_829_, v___x_824_);
v___x_831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_831_, 0, v___x_830_);
lean_ctor_set(v___x_831_, 1, v_a_810_);
return v___x_831_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______10___boxed(lean_object* v_x_832_, lean_object* v_a_833_, lean_object* v_a_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______10(v_x_832_, v_a_833_, v_a_834_);
lean_dec_ref(v_a_833_);
return v_res_835_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______11(lean_object* v_x_856_, lean_object* v_a_857_, lean_object* v_a_858_){
_start:
{
lean_object* v___x_859_; uint8_t v___x_860_; 
v___x_859_ = ((lean_object*)(l_Lean_termSatisfies__binder__pred_x25_____00__closed__1));
lean_inc(v_x_856_);
v___x_860_ = l_Lean_Syntax_isOfKind(v_x_856_, v___x_859_);
if (v___x_860_ == 0)
{
lean_object* v___x_861_; lean_object* v___x_862_; 
lean_dec(v_x_856_);
v___x_861_ = lean_box(1);
v___x_862_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_862_, 0, v___x_861_);
lean_ctor_set(v___x_862_, 1, v_a_858_);
return v___x_862_;
}
else
{
lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; uint8_t v___x_866_; 
v___x_863_ = lean_unsigned_to_nat(2u);
v___x_864_ = l_Lean_Syntax_getArg(v_x_856_, v___x_863_);
v___x_865_ = ((lean_object*)(l_Lean_binderPred_u2283___00__closed__1));
lean_inc(v___x_864_);
v___x_866_ = l_Lean_Syntax_isOfKind(v___x_864_, v___x_865_);
if (v___x_866_ == 0)
{
lean_object* v___x_867_; lean_object* v___x_868_; 
lean_dec(v___x_864_);
lean_dec(v_x_856_);
v___x_867_ = lean_box(1);
v___x_868_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_868_, 0, v___x_867_);
lean_ctor_set(v___x_868_, 1, v_a_858_);
return v___x_868_;
}
else
{
lean_object* v_ref_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; uint8_t v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; 
v_ref_869_ = lean_ctor_get(v_a_857_, 5);
v___x_870_ = lean_unsigned_to_nat(1u);
v___x_871_ = l_Lean_Syntax_getArg(v_x_856_, v___x_870_);
lean_dec(v_x_856_);
v___x_872_ = l_Lean_Syntax_getArg(v___x_864_, v___x_870_);
lean_dec(v___x_864_);
v___x_873_ = 0;
v___x_874_ = l_Lean_SourceInfo_fromRef(v_ref_869_, v___x_873_);
v___x_875_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______11___closed__1));
v___x_876_ = ((lean_object*)(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______11___closed__2));
lean_inc(v___x_874_);
v___x_877_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_877_, 0, v___x_874_);
lean_ctor_set(v___x_877_, 1, v___x_876_);
v___x_878_ = l_Lean_Syntax_node3(v___x_874_, v___x_875_, v___x_871_, v___x_877_, v___x_872_);
v___x_879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_879_, 0, v___x_878_);
lean_ctor_set(v___x_879_, 1, v_a_858_);
return v___x_879_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______11___boxed(lean_object* v_x_880_, lean_object* v_a_881_, lean_object* v_a_882_){
_start:
{
lean_object* v_res_883_; 
v_res_883_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______11(v_x_880_, v_a_881_, v_a_882_);
lean_dec_ref(v_a_881_);
return v_res_883_;
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

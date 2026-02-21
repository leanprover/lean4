// Lean compiler output
// Module: Lean.Elab.BuiltinDo.MatchExpr
// Imports: public import Lean.Elab.Do.Basic meta import Lean.Parser.Do import Lean.Elab.Do.PatternVar import Lean.Elab.BuiltinDo.Basic import Init.Omega
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
static const lean_string_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__0_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__1_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__2 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__2_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doLetExpr"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__3 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__3_value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__3_value),LEAN_SCALAR_PTR_LITERAL(68, 239, 85, 151, 235, 111, 29, 229)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__4 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__4_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "matchExprPat"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__5 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__6_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__5_value),LEAN_SCALAR_PTR_LITERAL(34, 152, 68, 102, 242, 224, 57, 35)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__6 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__6_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doMatchExpr"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__7 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__7_value),LEAN_SCALAR_PTR_LITERAL(72, 0, 49, 218, 206, 236, 229, 165)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__8 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__8_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "match_expr"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__9 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__9_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__10 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__10_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__10_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__11 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__11_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__12 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__12_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__13 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__13_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__14 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__14_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__15 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__15_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__16 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__16_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "with"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__17 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__17_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "matchExprAlts"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__18 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__18_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__19_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__19_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__19_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__18_value),LEAN_SCALAR_PTR_LITERAL(88, 158, 245, 158, 91, 207, 89, 187)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__19 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__19_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "matchExprAlt"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__20 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__20_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__21_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__21_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__21_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__21_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__20_value),LEAN_SCALAR_PTR_LITERAL(156, 165, 255, 22, 123, 199, 70, 61)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__21 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__21_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "|"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__22 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__22_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__23 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__23_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "matchExprElseAlt"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__24 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__24_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__25_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__25_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__25_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__25_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__24_value),LEAN_SCALAR_PTR_LITERAL(249, 132, 98, 23, 98, 205, 167, 22)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__25 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__25_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__26 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__26_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__27_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__27_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__27_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__27_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__26_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__27 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__27_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__28 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__28_value;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwUnsupported___redArg(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__0_value;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__1_value),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__2_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__2_value),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__4_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "BuiltinDo"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__5 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__4_value),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(104, 154, 37, 9, 26, 98, 187, 35)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__6 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__6_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "MatchExpr"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__7 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__6_value),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(143, 189, 152, 89, 18, 39, 213, 32)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__8 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__8_value;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(34, 157, 115, 249, 219, 101, 200, 85)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__9 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__9_value),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(3, 16, 195, 27, 23, 157, 197, 205)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__10 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__10_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__10_value),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(53, 176, 240, 177, 7, 187, 206, 173)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__11 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__11_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__12 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__12_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__11_value),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(233, 93, 19, 198, 66, 118, 152, 13)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__13 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__13_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "expandDoLetExpr"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__14 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__14_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__13_value),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(134, 253, 173, 213, 231, 15, 207, 23)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__15 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__15_value;
extern lean_object* l_Lean_Elab_macroAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___boxed(lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "doLetMetaExpr"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(231, 210, 172, 145, 91, 221, 30, 22)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___closed__1_value;
lean_object* l_Array_mkArray0(lean_object*);
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "expandDoLetMetaExpr"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__13_value),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 90, 112, 164, 175, 179, 176, 45)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr__1___boxed(lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "matchExpr"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___lam__0___closed__0_value;
lean_object* l_Lean_Elab_Do_mkMonadicType___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setArgs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___lam__0___boxed(lean_object**);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "match_expr else alternative"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___closed__0_value;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___lam__1___boxed(lean_object**);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "match_expr alternative "};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___closed__2 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___closed__3;
lean_object* l_Lean_Elab_Do_elabDoSeq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_doElabToSyntax___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_getExprPatternVarsEx___redArg(lean_object*);
lean_object* l_Lean_Elab_Do_checkMutVarsForShadowing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_DoElemCont_withDuplicableCont(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "__x"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(238, 215, 60, 46, 39, 217, 189, 106)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__1_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doExpr"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__2 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(130, 168, 60, 255, 153, 218, 88, 77)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__3 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__3_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__4 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__5 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__5_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "instantiateMVarsIfMVarApp"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__6 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__6_value;
lean_object* l_String_toRawSubstring_x27(lean_object*);
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__7;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__6_value),LEAN_SCALAR_PTR_LITERAL(180, 221, 231, 68, 33, 162, 30, 45)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__8 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__8_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__9 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__9_value;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__9_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__10_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__6_value),LEAN_SCALAR_PTR_LITERAL(97, 89, 84, 0, 241, 26, 4, 203)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__10 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__10_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__11 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__11_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__11_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__12 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__12_value;
lean_object* l_Lean_Elab_Do_inferControlInfoElem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_elabDoIdDecl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "elabDoMatchExpr"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__13_value),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(204, 115, 111, 111, 24, 156, 126, 219)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr__1___closed__1_value;
extern lean_object* l_Lean_Elab_Do_doElemElabAttribute;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__4));
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_1);
x_6 = l_Lean_Macro_throwUnsupported___redArg(x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = l_Lean_Syntax_getArg(x_1, x_7);
x_9 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__6));
lean_inc(x_8);
x_10 = l_Lean_Syntax_isOfKind(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_1);
x_11 = l_Lean_Macro_throwUnsupported___redArg(x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_unsigned_to_nat(6u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
lean_inc(x_13);
x_14 = l_Lean_Syntax_matchesNull(x_13, x_7);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_1);
x_15 = l_Lean_Macro_throwUnsupported___redArg(x_3);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_16 = lean_ctor_get(x_2, 5);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_unsigned_to_nat(3u);
x_19 = l_Lean_Syntax_getArg(x_1, x_18);
x_20 = lean_unsigned_to_nat(5u);
x_21 = l_Lean_Syntax_getArg(x_1, x_20);
lean_dec(x_1);
x_22 = l_Lean_Syntax_getArg(x_13, x_17);
lean_dec(x_13);
x_23 = 0;
x_24 = l_Lean_SourceInfo_fromRef(x_16, x_23);
x_25 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__8));
x_26 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__9));
lean_inc(x_24);
x_27 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_26);
x_28 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__11));
x_29 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__12));
lean_inc(x_24);
x_30 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_29);
x_31 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__13));
lean_inc(x_24);
x_32 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_32, 0, x_24);
lean_ctor_set(x_32, 1, x_31);
x_33 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__14));
lean_inc(x_24);
x_34 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_34, 0, x_24);
lean_ctor_set(x_34, 1, x_33);
x_35 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__15));
lean_inc(x_24);
x_36 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_36, 0, x_24);
lean_ctor_set(x_36, 1, x_35);
x_37 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__16));
lean_inc(x_24);
x_38 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_38, 0, x_24);
lean_ctor_set(x_38, 1, x_37);
lean_inc(x_24);
x_39 = l_Lean_Syntax_node5(x_24, x_28, x_30, x_32, x_34, x_36, x_38);
x_40 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__17));
lean_inc(x_24);
x_41 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_41, 0, x_24);
lean_ctor_set(x_41, 1, x_40);
x_42 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__19));
x_43 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__21));
x_44 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__22));
lean_inc(x_24);
x_45 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_45, 0, x_24);
lean_ctor_set(x_45, 1, x_44);
x_46 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__23));
lean_inc(x_24);
x_47 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_47, 0, x_24);
lean_ctor_set(x_47, 1, x_46);
lean_inc_ref(x_47);
lean_inc_ref(x_45);
lean_inc(x_24);
x_48 = l_Lean_Syntax_node4(x_24, x_43, x_45, x_8, x_47, x_22);
lean_inc(x_24);
x_49 = l_Lean_Syntax_node1(x_24, x_28, x_48);
x_50 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__25));
x_51 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__27));
x_52 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__28));
lean_inc(x_24);
x_53 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_53, 0, x_24);
lean_ctor_set(x_53, 1, x_52);
lean_inc(x_24);
x_54 = l_Lean_Syntax_node1(x_24, x_51, x_53);
lean_inc(x_24);
x_55 = l_Lean_Syntax_node4(x_24, x_50, x_45, x_54, x_47, x_21);
lean_inc(x_24);
x_56 = l_Lean_Syntax_node2(x_24, x_42, x_49, x_55);
x_57 = l_Lean_Syntax_node5(x_24, x_25, x_27, x_39, x_19, x_41, x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_3);
return x_58;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__4));
x_4 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__15));
x_5 = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___boxed), 3, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1();
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___closed__2(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Array_mkArray0(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___closed__1));
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_1);
x_6 = l_Lean_Macro_throwUnsupported___redArg(x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = l_Lean_Syntax_getArg(x_1, x_7);
x_9 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__6));
lean_inc(x_8);
x_10 = l_Lean_Syntax_isOfKind(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_1);
x_11 = l_Lean_Macro_throwUnsupported___redArg(x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_unsigned_to_nat(6u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
lean_inc(x_13);
x_14 = l_Lean_Syntax_matchesNull(x_13, x_7);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_1);
x_15 = l_Lean_Macro_throwUnsupported___redArg(x_3);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_16 = lean_ctor_get(x_2, 5);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_unsigned_to_nat(3u);
x_19 = l_Lean_Syntax_getArg(x_1, x_18);
x_20 = lean_unsigned_to_nat(5u);
x_21 = l_Lean_Syntax_getArg(x_1, x_20);
lean_dec(x_1);
x_22 = l_Lean_Syntax_getArg(x_13, x_17);
lean_dec(x_13);
x_23 = 0;
x_24 = l_Lean_SourceInfo_fromRef(x_16, x_23);
x_25 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__8));
x_26 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__9));
lean_inc(x_24);
x_27 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_26);
x_28 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__11));
x_29 = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___closed__2, &l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___closed__2_once, _init_l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___closed__2);
lean_inc(x_24);
x_30 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_28);
lean_ctor_set(x_30, 2, x_29);
x_31 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__17));
lean_inc(x_24);
x_32 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_32, 0, x_24);
lean_ctor_set(x_32, 1, x_31);
x_33 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__19));
x_34 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__21));
x_35 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__22));
lean_inc(x_24);
x_36 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_36, 0, x_24);
lean_ctor_set(x_36, 1, x_35);
x_37 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__23));
lean_inc(x_24);
x_38 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_38, 0, x_24);
lean_ctor_set(x_38, 1, x_37);
lean_inc_ref(x_38);
lean_inc_ref(x_36);
lean_inc(x_24);
x_39 = l_Lean_Syntax_node4(x_24, x_34, x_36, x_8, x_38, x_22);
lean_inc(x_24);
x_40 = l_Lean_Syntax_node1(x_24, x_28, x_39);
x_41 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__25));
x_42 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__27));
x_43 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__28));
lean_inc(x_24);
x_44 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_44, 0, x_24);
lean_ctor_set(x_44, 1, x_43);
lean_inc(x_24);
x_45 = l_Lean_Syntax_node1(x_24, x_42, x_44);
lean_inc(x_24);
x_46 = l_Lean_Syntax_node4(x_24, x_41, x_36, x_45, x_38, x_21);
lean_inc(x_24);
x_47 = l_Lean_Syntax_node2(x_24, x_33, x_40, x_46);
x_48 = l_Lean_Syntax_node5(x_24, x_25, x_27, x_30, x_19, x_32, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_3);
return x_49;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___closed__1));
x_4 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr__1___closed__1));
x_5 = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___boxed), 3, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr__1();
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch_spec__0___redArg___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_unsupportedSyntaxExceptionId;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch_spec__0___redArg() {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch_spec__0___redArg___closed__0);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch_spec__0___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch_spec__0___redArg();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch_spec__0___redArg();
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_20; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
if (lean_obj_tag(x_9) == 1)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_60 = lean_ctor_get(x_9, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_9, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_9, 2);
lean_inc_ref(x_62);
x_63 = lean_unsigned_to_nat(0u);
x_64 = lean_array_get_size(x_62);
x_65 = lean_nat_dec_lt(x_63, x_64);
if (x_65 == 0)
{
lean_dec_ref(x_10);
x_47 = x_9;
x_48 = x_60;
x_49 = x_61;
x_50 = x_62;
goto block_59;
}
else
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_9);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_67 = lean_ctor_get(x_9, 2);
lean_dec(x_67);
x_68 = lean_ctor_get(x_9, 1);
lean_dec(x_68);
x_69 = lean_ctor_get(x_9, 0);
lean_dec(x_69);
x_70 = lean_array_fget(x_62, x_63);
x_71 = lean_box(0);
x_72 = lean_array_fset(x_62, x_63, x_71);
x_73 = l_Lean_Syntax_setArgs(x_70, x_10);
x_74 = lean_array_fset(x_72, x_63, x_73);
lean_inc_ref(x_74);
lean_inc(x_61);
lean_inc(x_60);
lean_ctor_set(x_9, 2, x_74);
x_47 = x_9;
x_48 = x_60;
x_49 = x_61;
x_50 = x_74;
goto block_59;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_9);
x_75 = lean_array_fget(x_62, x_63);
x_76 = lean_box(0);
x_77 = lean_array_fset(x_62, x_63, x_76);
x_78 = l_Lean_Syntax_setArgs(x_75, x_10);
x_79 = lean_array_fset(x_77, x_63, x_78);
lean_inc_ref(x_79);
lean_inc(x_61);
lean_inc(x_60);
x_80 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_80, 0, x_60);
lean_ctor_set(x_80, 1, x_61);
lean_ctor_set(x_80, 2, x_79);
x_47 = x_80;
x_48 = x_60;
x_49 = x_61;
x_50 = x_79;
goto block_59;
}
}
}
else
{
lean_dec_ref(x_10);
if (lean_obj_tag(x_9) == 1)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_9, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_9, 1);
lean_inc(x_82);
x_83 = lean_ctor_get(x_9, 2);
lean_inc_ref(x_83);
x_47 = x_9;
x_48 = x_81;
x_49 = x_82;
x_50 = x_83;
goto block_59;
}
else
{
lean_dec(x_11);
x_20 = x_9;
goto block_46;
}
}
block_46:
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_12, 3);
lean_inc_ref(x_21);
x_22 = l_Lean_Elab_Do_mkMonadicType___redArg(x_21, x_12);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_24 = lean_ctor_get(x_17, 5);
x_25 = l_Lean_SourceInfo_fromRef(x_24, x_1);
x_26 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___lam__0___closed__0));
x_27 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_26);
x_28 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__9));
lean_inc(x_25);
x_29 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_29, 0, x_25);
lean_ctor_set(x_29, 1, x_28);
x_30 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__17));
lean_inc(x_25);
x_31 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_31, 0, x_25);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_Syntax_node4(x_25, x_27, x_29, x_5, x_31, x_20);
lean_ctor_set_tag(x_22, 1);
x_33 = l_Lean_Elab_Term_elabTerm(x_32, x_22, x_6, x_6, x_13, x_14, x_15, x_16, x_17, x_18);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_34 = lean_ctor_get(x_22, 0);
lean_inc(x_34);
lean_dec(x_22);
x_35 = lean_ctor_get(x_17, 5);
x_36 = l_Lean_SourceInfo_fromRef(x_35, x_1);
x_37 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___lam__0___closed__0));
x_38 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_37);
x_39 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__9));
lean_inc(x_36);
x_40 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_40, 0, x_36);
lean_ctor_set(x_40, 1, x_39);
x_41 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__17));
lean_inc(x_36);
x_42 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_42, 0, x_36);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lean_Syntax_node4(x_36, x_38, x_40, x_5, x_42, x_20);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_34);
x_45 = l_Lean_Elab_Term_elabTerm(x_43, x_44, x_6, x_6, x_13, x_14, x_15, x_16, x_17, x_18);
return x_45;
}
}
else
{
lean_dec(x_20);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_22;
}
}
block_59:
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_array_get_size(x_50);
x_52 = lean_nat_dec_lt(x_7, x_51);
if (x_52 == 0)
{
lean_dec_ref(x_50);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_11);
x_20 = x_47;
goto block_46;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_47);
x_53 = lean_array_fget(x_50, x_7);
x_54 = lean_box(0);
x_55 = lean_array_fset(x_50, x_7, x_54);
x_56 = l_Lean_Syntax_setArg(x_53, x_8, x_11);
x_57 = lean_array_fset(x_55, x_7, x_56);
x_58 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_58, 0, x_48);
lean_ctor_set(x_58, 1, x_49);
lean_ctor_set(x_58, 2, x_57);
x_20 = x_58;
goto block_46;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___lam__0___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
_start:
{
uint8_t x_20; uint8_t x_21; lean_object* x_22; 
x_20 = lean_unbox(x_1);
x_21 = lean_unbox(x_6);
x_22 = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___lam__0(x_20, x_2, x_3, x_4, x_5, x_21, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_8);
lean_dec(x_7);
return x_22;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___lam__1___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
lean_object* x_18; 
x_18 = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_4);
lean_dec(x_3);
return x_18;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_array_get_size(x_5);
x_15 = lean_nat_dec_lt(x_4, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_4);
x_16 = lean_unsigned_to_nat(1u);
x_17 = l_Lean_Syntax_getArg(x_2, x_16);
x_18 = lean_unsigned_to_nat(3u);
x_19 = l_Lean_Syntax_getArg(x_17, x_18);
lean_dec(x_17);
x_20 = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___closed__1, &l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___closed__1_once, _init_l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___closed__1);
x_21 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__0));
x_22 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__1));
x_23 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__2));
x_24 = 1;
x_25 = lean_box(x_15);
x_26 = lean_box(x_24);
x_27 = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___lam__0___boxed), 19, 10);
lean_closure_set(x_27, 0, x_25);
lean_closure_set(x_27, 1, x_21);
lean_closure_set(x_27, 2, x_22);
lean_closure_set(x_27, 3, x_23);
lean_closure_set(x_27, 4, x_1);
lean_closure_set(x_27, 5, x_26);
lean_closure_set(x_27, 6, x_16);
lean_closure_set(x_27, 7, x_18);
lean_closure_set(x_27, 8, x_2);
lean_closure_set(x_27, 9, x_5);
x_28 = lean_box(x_24);
lean_inc(x_19);
x_29 = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoSeq___boxed), 11, 3);
lean_closure_set(x_29, 0, x_19);
lean_closure_set(x_29, 1, x_3);
lean_closure_set(x_29, 2, x_28);
x_30 = l_Lean_Elab_Do_doElabToSyntax___redArg(x_20, x_29, x_27, x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_19);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_array_fget(x_5, x_4);
x_32 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__21));
lean_inc(x_31);
x_33 = l_Lean_Syntax_isOfKind(x_31, x_32);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_31);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_34 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch_spec__0___redArg();
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_unsigned_to_nat(1u);
x_36 = l_Lean_Syntax_getArg(x_31, x_35);
lean_inc(x_36);
x_37 = l_Lean_Elab_Do_getExprPatternVarsEx___redArg(x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
lean_inc_ref(x_11);
x_39 = l_Lean_Elab_Do_checkMutVarsForShadowing(x_38, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec_ref(x_39);
lean_inc_ref(x_3);
lean_inc(x_36);
x_40 = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___lam__1___boxed), 17, 8);
lean_closure_set(x_40, 0, x_32);
lean_closure_set(x_40, 1, x_36);
lean_closure_set(x_40, 2, x_4);
lean_closure_set(x_40, 3, x_35);
lean_closure_set(x_40, 4, x_5);
lean_closure_set(x_40, 5, x_1);
lean_closure_set(x_40, 6, x_2);
lean_closure_set(x_40, 7, x_3);
x_41 = lean_unsigned_to_nat(3u);
x_42 = l_Lean_Syntax_getArg(x_31, x_41);
lean_dec(x_31);
x_43 = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___closed__3, &l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___closed__3_once, _init_l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___closed__3);
x_44 = l_Lean_MessageData_ofSyntax(x_36);
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_box(x_33);
lean_inc(x_42);
x_47 = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoSeq___boxed), 11, 3);
lean_closure_set(x_47, 0, x_42);
lean_closure_set(x_47, 1, x_3);
lean_closure_set(x_47, 2, x_46);
x_48 = l_Lean_Elab_Do_doElabToSyntax___redArg(x_45, x_47, x_40, x_42, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_42);
return x_48;
}
else
{
uint8_t x_49; 
lean_dec(x_36);
lean_dec(x_31);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_39);
if (x_49 == 0)
{
return x_39;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_39, 0);
lean_inc(x_50);
lean_dec(x_39);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_36);
lean_dec(x_31);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_37);
if (x_52 == 0)
{
return x_37;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_37, 0);
lean_inc(x_53);
lean_dec(x_37);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
return x_54;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_18 = lean_ctor_get(x_15, 5);
x_19 = 0;
x_20 = l_Lean_SourceInfo_fromRef(x_18, x_19);
x_21 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__22));
lean_inc(x_20);
x_22 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__23));
lean_inc(x_20);
x_24 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_Syntax_node4(x_20, x_1, x_22, x_2, x_24, x_9);
x_26 = lean_nat_add(x_3, x_4);
x_27 = lean_array_fset(x_5, x_3, x_25);
x_28 = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch(x_6, x_7, x_8, x_26, x_27, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_28;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_10 = lean_array_uset(x_7, x_2, x_5);
x_2 = x_9;
x_3 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
x_14 = l_Lean_Syntax_getArgs(x_13);
lean_dec(x_13);
x_15 = lean_array_size(x_14);
x_16 = 0;
x_17 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_spec__0(x_15, x_16, x_14);
x_18 = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch(x_2, x_1, x_3, x_12, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_18;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta___lam__0___boxed), 11, 2);
lean_closure_set(x_13, 0, x_3);
lean_closure_set(x_13, 1, x_2);
x_14 = l_Lean_Elab_Do_DoElemCont_withDuplicableCont(x_4, x_1, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__6));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_11 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__8));
lean_inc(x_1);
x_12 = l_Lean_Syntax_isOfKind(x_1, x_11);
if (x_12 == 0)
{
lean_object* x_61; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_61 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch_spec__0___redArg();
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_62 = lean_unsigned_to_nat(1u);
x_63 = l_Lean_Syntax_getArg(x_1, x_62);
x_64 = l_Lean_Syntax_isNone(x_63);
if (x_64 == 0)
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_unsigned_to_nat(5u);
lean_inc(x_63);
x_66 = l_Lean_Syntax_matchesNull(x_63, x_65);
if (x_66 == 0)
{
lean_object* x_67; 
lean_dec(x_63);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_67 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch_spec__0___redArg();
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_unsigned_to_nat(4u);
x_69 = l_Lean_Syntax_getArg(x_63, x_68);
lean_dec(x_63);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_69);
x_13 = x_70;
x_14 = x_3;
x_15 = x_4;
x_16 = x_5;
x_17 = x_6;
x_18 = x_7;
x_19 = x_8;
x_20 = x_9;
x_21 = lean_box(0);
goto block_60;
}
}
else
{
lean_object* x_71; 
lean_dec(x_63);
x_71 = lean_box(0);
x_13 = x_71;
x_14 = x_3;
x_15 = x_4;
x_16 = x_5;
x_17 = x_6;
x_18 = x_7;
x_19 = x_8;
x_20 = x_9;
x_21 = lean_box(0);
goto block_60;
}
}
block_60:
{
lean_object* x_22; 
lean_inc(x_20);
lean_inc_ref(x_19);
lean_inc(x_18);
lean_inc_ref(x_17);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_1);
x_22 = l_Lean_Elab_Do_inferControlInfoElem(x_1, x_15, x_16, x_17, x_18, x_19, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = lean_unsigned_to_nat(2u);
x_25 = l_Lean_Syntax_getArg(x_1, x_24);
x_26 = lean_unsigned_to_nat(4u);
x_27 = l_Lean_Syntax_getArg(x_1, x_26);
lean_dec(x_1);
if (lean_obj_tag(x_13) == 0)
{
if (x_12 == 0)
{
lean_object* x_28; 
x_28 = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta(x_23, x_25, x_27, x_2, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__1));
lean_inc(x_20);
lean_inc_ref(x_19);
x_30 = l_Lean_Core_mkFreshUserName(x_29, x_19, x_20);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec_ref(x_30);
x_32 = lean_ctor_get(x_19, 5);
x_33 = lean_ctor_get(x_19, 10);
x_34 = lean_ctor_get(x_19, 11);
x_35 = 0;
x_36 = l_Lean_mkIdentFrom(x_25, x_31, x_35);
x_37 = l_Lean_SourceInfo_fromRef(x_32, x_35);
x_38 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__3));
x_39 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__5));
x_40 = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__7, &l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__7_once, _init_l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__7);
x_41 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__8));
lean_inc(x_34);
lean_inc(x_33);
x_42 = l_Lean_addMacroScope(x_33, x_41, x_34);
x_43 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__12));
lean_inc(x_37);
x_44 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_44, 0, x_37);
lean_ctor_set(x_44, 1, x_40);
lean_ctor_set(x_44, 2, x_42);
lean_ctor_set(x_44, 3, x_43);
x_45 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__11));
lean_inc(x_37);
x_46 = l_Lean_Syntax_node1(x_37, x_45, x_25);
lean_inc(x_37);
x_47 = l_Lean_Syntax_node2(x_37, x_39, x_44, x_46);
x_48 = l_Lean_Syntax_node1(x_37, x_38, x_47);
x_49 = lean_box(0);
lean_inc(x_36);
x_50 = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta___boxed), 12, 4);
lean_closure_set(x_50, 0, x_23);
lean_closure_set(x_50, 1, x_36);
lean_closure_set(x_50, 2, x_27);
lean_closure_set(x_50, 3, x_2);
x_51 = 0;
x_52 = l_Lean_Elab_Do_elabDoIdDecl(x_36, x_49, x_48, x_50, x_51, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
return x_52;
}
else
{
uint8_t x_53; 
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_2);
x_53 = !lean_is_exclusive(x_30);
if (x_53 == 0)
{
return x_30;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_30, 0);
lean_inc(x_54);
lean_dec(x_30);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
}
}
}
else
{
lean_object* x_56; 
lean_dec_ref(x_13);
x_56 = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta(x_23, x_25, x_27, x_2, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
return x_56;
}
}
else
{
uint8_t x_57; 
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_2);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_22);
if (x_57 == 0)
{
return x_22;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_22, 0);
lean_inc(x_58);
lean_dec(x_22);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
return x_59;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Do_doElemElabAttribute;
x_3 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__8));
x_4 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr__1___closed__1));
x_5 = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___boxed), 10, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr__1();
return x_2;
}
}
lean_object* initialize_Lean_Elab_Do_Basic(uint8_t builtin);
lean_object* initialize_Lean_Parser_Do(uint8_t builtin);
lean_object* initialize_Lean_Elab_Do_PatternVar(uint8_t builtin);
lean_object* initialize_Lean_Elab_BuiltinDo_Basic(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_BuiltinDo_MatchExpr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Do_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Do_PatternVar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_BuiltinDo_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

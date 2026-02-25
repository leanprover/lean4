// Lean compiler output
// Module: Init.WFTactics
// Imports: public import Init.WF public import Init.Data.Nat.Basic
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
static const lean_string_object l_tacticSimp__wf___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "tacticSimp_wf"};
static const lean_object* l_tacticSimp__wf___closed__0 = (const lean_object*)&l_tacticSimp__wf___closed__0_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_tacticSimp__wf___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_tacticSimp__wf___closed__0_value),LEAN_SCALAR_PTR_LITERAL(226, 142, 199, 78, 176, 208, 194, 249)}};
static const lean_object* l_tacticSimp__wf___closed__1 = (const lean_object*)&l_tacticSimp__wf___closed__1_value;
static const lean_string_object l_tacticSimp__wf___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "simp_wf"};
static const lean_object* l_tacticSimp__wf___closed__2 = (const lean_object*)&l_tacticSimp__wf___closed__2_value;
static const lean_ctor_object l_tacticSimp__wf___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_tacticSimp__wf___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_tacticSimp__wf___closed__3 = (const lean_object*)&l_tacticSimp__wf___closed__3_value;
static const lean_ctor_object l_tacticSimp__wf___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_tacticSimp__wf___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_tacticSimp__wf___closed__3_value)}};
static const lean_object* l_tacticSimp__wf___closed__4 = (const lean_object*)&l_tacticSimp__wf___closed__4_value;
LEAN_EXPORT const lean_object* l_tacticSimp__wf = (const lean_object*)&l_tacticSimp__wf___closed__4_value;
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__0 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__0_value;
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__1 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__1_value;
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__2 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__2_value;
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "tacticTry_"};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__3 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__3_value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__4_value_aux_0),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__4_value_aux_1),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__4_value_aux_2),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(34, 109, 187, 155, 23, 130, 33, 152)}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__4 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__4_value;
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "try"};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__5 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__5_value;
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__6 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__6_value;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__7_value_aux_0),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__7_value_aux_1),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__7_value_aux_2),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__7 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__7_value;
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__8 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__8_value;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__9_value_aux_0),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__9_value_aux_1),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__9_value_aux_2),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__9 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__9_value;
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__10 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__10_value;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__11 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__11_value;
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__12 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__12_value;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__13_value_aux_0),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__13_value_aux_1),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__13_value_aux_2),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(50, 13, 241, 145, 67, 153, 105, 177)}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__13 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__13_value;
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__14 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__14_value;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__15_value_aux_0),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__15_value_aux_1),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__15_value_aux_2),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__15 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__15_value;
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "configItem"};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__16 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__16_value;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__17_value_aux_0),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__17_value_aux_1),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__17_value_aux_2),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(205, 9, 236, 192, 59, 252, 178, 140)}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__17 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__17_value;
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "posConfigItem"};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__18 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__18_value;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__19_value_aux_0),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__19_value_aux_1),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__19_value_aux_2),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(232, 137, 50, 117, 152, 182, 155, 132)}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__19 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__19_value;
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "+"};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__20 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__20_value;
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "unfoldPartialApp"};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__21 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__21_value;
lean_object* l_String_toRawSubstring_x27(lean_object*);
static lean_once_cell_t l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__22;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(49, 203, 120, 209, 69, 128, 204, 215)}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__23 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__23_value;
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "zetaDelta"};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__24 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__24_value;
static lean_once_cell_t l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__25;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__24_value),LEAN_SCALAR_PTR_LITERAL(129, 80, 40, 32, 247, 216, 203, 14)}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__26 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__26_value;
lean_object* l_Array_mkArray0(lean_object*);
static lean_once_cell_t l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__27;
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__28 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__28_value;
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "simpLemma"};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__29 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__29_value;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__30_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__30_value_aux_0),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__30_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__30_value_aux_1),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__30_value_aux_2),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__29_value),LEAN_SCALAR_PTR_LITERAL(38, 215, 101, 250, 181, 108, 118, 102)}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__30 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__30_value;
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "invImage"};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__31 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__31_value;
static lean_once_cell_t l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__32;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__31_value),LEAN_SCALAR_PTR_LITERAL(115, 194, 127, 152, 147, 1, 182, 44)}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__33 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__33_value;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__33_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__34 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__34_value;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__34_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__35 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__35_value;
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__36 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__36_value;
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "InvImage"};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__37 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__37_value;
static lean_once_cell_t l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__38;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__37_value),LEAN_SCALAR_PTR_LITERAL(139, 185, 23, 6, 110, 176, 215, 49)}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__39 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__39_value;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__39_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__40 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__40_value;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__39_value)}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__41 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__41_value;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__41_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__42 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__42_value;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__40_value),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__42_value)}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__43 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__43_value;
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Prod.lex"};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__44 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__44_value;
static lean_once_cell_t l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__45;
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Prod"};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__46 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__46_value;
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "lex"};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__47 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__47_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__48_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__46_value),LEAN_SCALAR_PTR_LITERAL(121, 119, 164, 206, 221, 118, 48, 212)}};
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__48_value_aux_0),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__47_value),LEAN_SCALAR_PTR_LITERAL(198, 90, 40, 255, 65, 117, 114, 239)}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__48 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__48_value;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__48_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__49 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__49_value;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__48_value)}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__50 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__50_value;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__50_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__51 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__51_value;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__49_value),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__51_value)}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__52 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__52_value;
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "sizeOfWFRel"};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__53 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__53_value;
static lean_once_cell_t l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__54_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__54;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__53_value),LEAN_SCALAR_PTR_LITERAL(194, 78, 238, 176, 11, 67, 192, 104)}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__55 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__55_value;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__55_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__56 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__56_value;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__56_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__57 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__57_value;
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "measure"};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__58 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__58_value;
static lean_once_cell_t l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__59_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__59;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__58_value),LEAN_SCALAR_PTR_LITERAL(20, 255, 171, 227, 253, 115, 152, 82)}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__60 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__60_value;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__60_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__61 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__61_value;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__61_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__62 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__62_value;
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Nat.lt_wfRel"};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__63 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__63_value;
static lean_once_cell_t l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__64_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__64;
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__65 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__65_value;
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "lt_wfRel"};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__66 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__66_value;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__67_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__65_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__67_value_aux_0),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__66_value),LEAN_SCALAR_PTR_LITERAL(154, 103, 103, 42, 122, 250, 41, 80)}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__67 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__67_value;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__67_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__68 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__68_value;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__68_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__69 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__69_value;
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "WellFoundedRelation.rel"};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__70 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__70_value;
static lean_once_cell_t l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__71_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__71;
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "WellFoundedRelation"};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__72 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__72_value;
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rel"};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__73 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__73_value;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__74_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__72_value),LEAN_SCALAR_PTR_LITERAL(247, 146, 95, 132, 177, 137, 153, 47)}};
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__74_value_aux_0),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__73_value),LEAN_SCALAR_PTR_LITERAL(149, 61, 97, 242, 68, 92, 238, 81)}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__74 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__74_value;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__74_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__75 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__75_value;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__75_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__76 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__76_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_once_cell_t l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__77_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__77;
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__78_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__78 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__78_value;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_tacticClean__wf___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "tacticClean_wf"};
static const lean_object* l_tacticClean__wf___closed__0 = (const lean_object*)&l_tacticClean__wf___closed__0_value;
static const lean_ctor_object l_tacticClean__wf___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_tacticClean__wf___closed__0_value),LEAN_SCALAR_PTR_LITERAL(17, 233, 161, 8, 11, 18, 19, 159)}};
static const lean_object* l_tacticClean__wf___closed__1 = (const lean_object*)&l_tacticClean__wf___closed__1_value;
static const lean_string_object l_tacticClean__wf___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "clean_wf"};
static const lean_object* l_tacticClean__wf___closed__2 = (const lean_object*)&l_tacticClean__wf___closed__2_value;
static const lean_ctor_object l_tacticClean__wf___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_tacticClean__wf___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_tacticClean__wf___closed__3 = (const lean_object*)&l_tacticClean__wf___closed__3_value;
static const lean_ctor_object l_tacticClean__wf___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_tacticClean__wf___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_tacticClean__wf___closed__3_value)}};
static const lean_object* l_tacticClean__wf___closed__4 = (const lean_object*)&l_tacticClean__wf___closed__4_value;
LEAN_EXPORT const lean_object* l_tacticClean__wf = (const lean_object*)&l_tacticClean__wf___closed__4_value;
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "negConfigItem"};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__0 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__0_value;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__1_value_aux_0),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__1_value_aux_1),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__1_value_aux_2),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(196, 29, 29, 161, 247, 206, 181, 221)}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__1 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__1_value;
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__2 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__2_value;
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "failIfUnchanged"};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__3 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__3_value;
static lean_once_cell_t l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__4;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(6, 104, 167, 161, 191, 186, 8, 81)}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__5 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__5_value;
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "only"};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__6 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__6_value;
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "sizeOf_nat"};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__7 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__7_value;
static lean_once_cell_t l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__8;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(48, 100, 48, 136, 48, 232, 239, 45)}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__9 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__9_value;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__10 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__10_value;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__11 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__11_value;
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "reduceCtorEq"};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__12 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__12_value;
static lean_once_cell_t l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__13;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(241, 230, 128, 19, 70, 224, 61, 3)}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__14 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__14_value;
static lean_once_cell_t l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__15;
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticClean__wf__1(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_tacticDecreasing__trivial___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "tacticDecreasing_trivial"};
static const lean_object* l_tacticDecreasing__trivial___closed__0 = (const lean_object*)&l_tacticDecreasing__trivial___closed__0_value;
static const lean_ctor_object l_tacticDecreasing__trivial___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_tacticDecreasing__trivial___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 43, 154, 34, 2, 43, 185, 79)}};
static const lean_object* l_tacticDecreasing__trivial___closed__1 = (const lean_object*)&l_tacticDecreasing__trivial___closed__1_value;
static const lean_string_object l_tacticDecreasing__trivial___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "decreasing_trivial"};
static const lean_object* l_tacticDecreasing__trivial___closed__2 = (const lean_object*)&l_tacticDecreasing__trivial___closed__2_value;
static const lean_ctor_object l_tacticDecreasing__trivial___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_tacticDecreasing__trivial___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_tacticDecreasing__trivial___closed__3 = (const lean_object*)&l_tacticDecreasing__trivial___closed__3_value;
static const lean_ctor_object l_tacticDecreasing__trivial___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_tacticDecreasing__trivial___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_tacticDecreasing__trivial___closed__3_value)}};
static const lean_object* l_tacticDecreasing__trivial___closed__4 = (const lean_object*)&l_tacticDecreasing__trivial___closed__4_value;
LEAN_EXPORT const lean_object* l_tacticDecreasing__trivial = (const lean_object*)&l_tacticDecreasing__trivial___closed__4_value;
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "tactic_<;>_"};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__0 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__0_value;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__1_value_aux_0),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__1_value_aux_1),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__1_value_aux_2),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(31, 118, 44, 159, 195, 11, 47, 176)}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__1 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__1_value;
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__2 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__2_value;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__3_value_aux_0),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__3_value_aux_1),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__3_value_aux_2),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(117, 253, 122, 28, 77, 248, 149, 120)}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__3 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__3_value;
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__4 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__4_value;
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "arith"};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__5 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__5_value;
static lean_once_cell_t l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__6;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(72, 221, 106, 103, 22, 21, 224, 51)}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__7 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__7_value;
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__8 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__8_value;
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "<;>"};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__9 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__9_value;
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "done"};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__10 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__10_value;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__11_value_aux_0),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__11_value_aux_1),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__11_value_aux_2),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(113, 161, 179, 82, 204, 87, 48, 123)}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__11 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__11_value;
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "omega"};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__2___closed__0 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__2___closed__0_value;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__2___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__2___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__2___closed__1_value_aux_0),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__2___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__2___closed__1_value_aux_1),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__2___closed__1_value_aux_2),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(138, 49, 229, 237, 137, 52, 176, 206)}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__2___closed__1 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__2___closed__1_value;
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "assumption"};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___closed__0 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___closed__0_value;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___closed__1_value_aux_0),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___closed__1_value_aux_1),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___closed__1_value_aux_2),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(240, 50, 167, 190, 65, 82, 149, 231)}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___closed__1 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___closed__1_value;
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_tacticDecreasing__trivial__pre__omega___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "tacticDecreasing_trivial_pre_omega"};
static const lean_object* l_tacticDecreasing__trivial__pre__omega___closed__0 = (const lean_object*)&l_tacticDecreasing__trivial__pre__omega___closed__0_value;
static const lean_ctor_object l_tacticDecreasing__trivial__pre__omega___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_tacticDecreasing__trivial__pre__omega___closed__0_value),LEAN_SCALAR_PTR_LITERAL(24, 217, 244, 248, 29, 160, 44, 47)}};
static const lean_object* l_tacticDecreasing__trivial__pre__omega___closed__1 = (const lean_object*)&l_tacticDecreasing__trivial__pre__omega___closed__1_value;
static const lean_string_object l_tacticDecreasing__trivial__pre__omega___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "decreasing_trivial_pre_omega"};
static const lean_object* l_tacticDecreasing__trivial__pre__omega___closed__2 = (const lean_object*)&l_tacticDecreasing__trivial__pre__omega___closed__2_value;
static const lean_ctor_object l_tacticDecreasing__trivial__pre__omega___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_tacticDecreasing__trivial__pre__omega___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_tacticDecreasing__trivial__pre__omega___closed__3 = (const lean_object*)&l_tacticDecreasing__trivial__pre__omega___closed__3_value;
static const lean_ctor_object l_tacticDecreasing__trivial__pre__omega___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_tacticDecreasing__trivial__pre__omega___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_tacticDecreasing__trivial__pre__omega___closed__3_value)}};
static const lean_object* l_tacticDecreasing__trivial__pre__omega___closed__4 = (const lean_object*)&l_tacticDecreasing__trivial__pre__omega___closed__4_value;
LEAN_EXPORT const lean_object* l_tacticDecreasing__trivial__pre__omega = (const lean_object*)&l_tacticDecreasing__trivial__pre__omega___closed__4_value;
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "seq1"};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__0 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__0_value;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__1_value_aux_0),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__1_value_aux_1),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__1_value_aux_2),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(242, 140, 137, 56, 141, 11, 143, 117)}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__1 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__1_value;
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "apply"};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__2 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__2_value;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__3_value_aux_0),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__3_value_aux_1),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__3_value_aux_2),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(202, 125, 237, 78, 179, 140, 218, 80)}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__3 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__3_value;
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Nat.sub_succ_lt_self"};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__4 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__4_value;
static lean_once_cell_t l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__5;
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "sub_succ_lt_self"};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__6 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__6_value;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__65_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__7_value_aux_0),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(225, 190, 144, 22, 170, 162, 65, 171)}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__7 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__7_value;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__7_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__8 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__8_value;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__9 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__9_value;
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ";"};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__10 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__10_value;
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Nat.pred_lt_of_lt"};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__0 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__0_value;
static lean_once_cell_t l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__1;
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "pred_lt_of_lt"};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__2 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__2_value;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__65_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__3_value_aux_0),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(12, 26, 157, 71, 38, 184, 184, 53)}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__3 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__3_value;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__4 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__4_value;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__5 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__5_value;
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Nat.pred_lt"};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__0 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__0_value;
static lean_once_cell_t l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__1;
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "pred_lt"};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__2 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__2_value;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__65_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__3_value_aux_0),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(236, 238, 157, 223, 210, 179, 121, 158)}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__3 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__3_value;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__4 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__4_value;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__5 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__5_value;
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_tacticDecreasing__with___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "tacticDecreasing_with_"};
static const lean_object* l_tacticDecreasing__with___00__closed__0 = (const lean_object*)&l_tacticDecreasing__with___00__closed__0_value;
static const lean_ctor_object l_tacticDecreasing__with___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_tacticDecreasing__with___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(24, 61, 177, 33, 212, 229, 232, 236)}};
static const lean_object* l_tacticDecreasing__with___00__closed__1 = (const lean_object*)&l_tacticDecreasing__with___00__closed__1_value;
static const lean_string_object l_tacticDecreasing__with___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_tacticDecreasing__with___00__closed__2 = (const lean_object*)&l_tacticDecreasing__with___00__closed__2_value;
static const lean_ctor_object l_tacticDecreasing__with___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_tacticDecreasing__with___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_tacticDecreasing__with___00__closed__3 = (const lean_object*)&l_tacticDecreasing__with___00__closed__3_value;
static const lean_string_object l_tacticDecreasing__with___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "decreasing_with "};
static const lean_object* l_tacticDecreasing__with___00__closed__4 = (const lean_object*)&l_tacticDecreasing__with___00__closed__4_value;
static const lean_ctor_object l_tacticDecreasing__with___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_tacticDecreasing__with___00__closed__4_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_tacticDecreasing__with___00__closed__5 = (const lean_object*)&l_tacticDecreasing__with___00__closed__5_value;
static const lean_ctor_object l_tacticDecreasing__with___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(13, 106, 54, 236, 164, 218, 24, 154)}};
static const lean_object* l_tacticDecreasing__with___00__closed__6 = (const lean_object*)&l_tacticDecreasing__with___00__closed__6_value;
static const lean_ctor_object l_tacticDecreasing__with___00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_tacticDecreasing__with___00__closed__6_value)}};
static const lean_object* l_tacticDecreasing__with___00__closed__7 = (const lean_object*)&l_tacticDecreasing__with___00__closed__7_value;
static const lean_ctor_object l_tacticDecreasing__with___00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_tacticDecreasing__with___00__closed__3_value),((lean_object*)&l_tacticDecreasing__with___00__closed__5_value),((lean_object*)&l_tacticDecreasing__with___00__closed__7_value)}};
static const lean_object* l_tacticDecreasing__with___00__closed__8 = (const lean_object*)&l_tacticDecreasing__with___00__closed__8_value;
static const lean_ctor_object l_tacticDecreasing__with___00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_tacticDecreasing__with___00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_tacticDecreasing__with___00__closed__8_value)}};
static const lean_object* l_tacticDecreasing__with___00__closed__9 = (const lean_object*)&l_tacticDecreasing__with___00__closed__9_value;
LEAN_EXPORT const lean_object* l_tacticDecreasing__with__ = (const lean_object*)&l_tacticDecreasing__with___00__closed__9_value;
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "tacticRepeat_"};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__0 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__0_value;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__1_value_aux_0),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__1_value_aux_1),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__1_value_aux_2),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(149, 101, 42, 245, 144, 172, 68, 230)}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__1 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__1_value;
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "repeat"};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__2 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__2_value;
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "first"};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__3 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__3_value;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__4_value_aux_0),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__4_value_aux_1),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__4_value_aux_2),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(59, 232, 35, 17, 172, 62, 48, 174)}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__4 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__4_value;
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "group"};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__5 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__5_value;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(206, 113, 20, 57, 188, 177, 187, 30)}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__6 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__6_value;
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "|"};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__7 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__7_value;
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Prod.Lex.right"};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__8 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__8_value;
static lean_once_cell_t l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__9;
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Lex"};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__10 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__10_value;
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "right"};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__11 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__11_value;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__46_value),LEAN_SCALAR_PTR_LITERAL(121, 119, 164, 206, 221, 118, 48, 212)}};
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__12_value_aux_0),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(197, 185, 120, 51, 217, 37, 16, 88)}};
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__12_value_aux_1),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__11_value),LEAN_SCALAR_PTR_LITERAL(150, 130, 116, 62, 23, 117, 165, 123)}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__12 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__12_value;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__12_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__13 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__13_value;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__13_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__14 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__14_value;
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Prod.Lex.left"};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__15 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__15_value;
static lean_once_cell_t l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__16;
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "left"};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__17 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__17_value;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__46_value),LEAN_SCALAR_PTR_LITERAL(121, 119, 164, 206, 221, 118, 48, 212)}};
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__18_value_aux_0),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(197, 185, 120, 51, 217, 37, 16, 88)}};
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__18_value_aux_1),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__17_value),LEAN_SCALAR_PTR_LITERAL(72, 8, 133, 98, 148, 81, 57, 220)}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__18 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__18_value;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__18_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__19 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__19_value;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__19_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__20 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__20_value;
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "PSigma.Lex.right"};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__21 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__21_value;
static lean_once_cell_t l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__22;
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "PSigma"};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__23 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__23_value;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__23_value),LEAN_SCALAR_PTR_LITERAL(0, 171, 149, 177, 120, 131, 37, 223)}};
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__24_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__24_value_aux_0),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(168, 119, 214, 24, 36, 134, 16, 11)}};
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__24_value_aux_1),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__11_value),LEAN_SCALAR_PTR_LITERAL(207, 69, 96, 239, 196, 165, 12, 72)}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__24 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__24_value;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__24_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__25 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__25_value;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__25_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__26 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__26_value;
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "PSigma.Lex.left"};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__27 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__27_value;
static lean_once_cell_t l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__28;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__23_value),LEAN_SCALAR_PTR_LITERAL(0, 171, 149, 177, 120, 131, 37, 223)}};
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__29_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__29_value_aux_0),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(168, 119, 214, 24, 36, 134, 16, 11)}};
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__29_value_aux_1),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__17_value),LEAN_SCALAR_PTR_LITERAL(41, 188, 239, 98, 108, 77, 28, 32)}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__29 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__29_value;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__29_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__30 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__30_value;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__30_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__31 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__31_value;
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "fail"};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__32 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__32_value;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__33_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__33_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__33_value_aux_0),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__33_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__33_value_aux_1),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__33_value_aux_2),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__32_value),LEAN_SCALAR_PTR_LITERAL(251, 214, 242, 89, 226, 36, 213, 0)}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__33 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__33_value;
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__34 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__34_value;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__34_value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__35 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__35_value;
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 262, .m_capacity = 262, .m_length = 261, .m_data = "\"failed to prove termination, possible solutions:\n  - Use `have`-expressions to prove the remaining goals\n  - Use `termination_by` to specify a different well-founded relation\n  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal\""};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__36 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__36_value;
static lean_once_cell_t l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__37;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_tacticDecreasing__tactic___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "tacticDecreasing_tactic"};
static const lean_object* l_tacticDecreasing__tactic___closed__0 = (const lean_object*)&l_tacticDecreasing__tactic___closed__0_value;
static const lean_ctor_object l_tacticDecreasing__tactic___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_tacticDecreasing__tactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(19, 100, 186, 108, 185, 30, 251, 120)}};
static const lean_object* l_tacticDecreasing__tactic___closed__1 = (const lean_object*)&l_tacticDecreasing__tactic___closed__1_value;
static const lean_string_object l_tacticDecreasing__tactic___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "decreasing_tactic"};
static const lean_object* l_tacticDecreasing__tactic___closed__2 = (const lean_object*)&l_tacticDecreasing__tactic___closed__2_value;
static const lean_ctor_object l_tacticDecreasing__tactic___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_tacticDecreasing__tactic___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_tacticDecreasing__tactic___closed__3 = (const lean_object*)&l_tacticDecreasing__tactic___closed__3_value;
static const lean_ctor_object l_tacticDecreasing__tactic___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_tacticDecreasing__tactic___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_tacticDecreasing__tactic___closed__3_value)}};
static const lean_object* l_tacticDecreasing__tactic___closed__4 = (const lean_object*)&l_tacticDecreasing__tactic___closed__4_value;
LEAN_EXPORT const lean_object* l_tacticDecreasing__tactic = (const lean_object*)&l_tacticDecreasing__tactic___closed__4_value;
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "decreasing_with"};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___closed__0 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___closed__0_value;
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "substVars"};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___closed__1 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___closed__1_value;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___closed__2_value_aux_0),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___closed__2_value_aux_1),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___closed__2_value_aux_2),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(164, 80, 240, 20, 13, 181, 46, 131)}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___closed__2 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___closed__2_value;
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "subst_vars"};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___closed__3 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___closed__3_value;
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__22(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__21));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__25(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__24));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__27(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Array_mkArray0(lean_box(0));
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__32(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__31));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__38(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__37));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__45(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__44));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__54(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__53));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__59(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__58));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__64(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__63));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__71(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__70));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__77(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(13u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = ((lean_object*)(l_tacticSimp__wf___closed__1));
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec_ref(x_2);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 5);
lean_inc(x_10);
lean_dec_ref(x_2);
x_11 = 0;
x_12 = l_Lean_SourceInfo_fromRef(x_10, x_11);
lean_dec(x_10);
x_13 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__4));
x_14 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__5));
lean_inc(x_12);
x_15 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
x_16 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__7));
x_17 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__9));
x_18 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__11));
x_19 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__12));
x_20 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__13));
lean_inc(x_12);
x_21 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_21, 0, x_12);
lean_ctor_set(x_21, 1, x_19);
x_22 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__15));
x_23 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__17));
x_24 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__19));
x_25 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__20));
lean_inc(x_12);
x_26 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_26, 0, x_12);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__22, &l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__22_once, _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__22);
x_28 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__23));
lean_inc(x_9);
lean_inc(x_8);
x_29 = l_Lean_addMacroScope(x_8, x_28, x_9);
x_30 = lean_box(0);
lean_inc(x_12);
x_31 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_31, 0, x_12);
lean_ctor_set(x_31, 1, x_27);
lean_ctor_set(x_31, 2, x_29);
lean_ctor_set(x_31, 3, x_30);
lean_inc_ref(x_26);
lean_inc(x_12);
x_32 = l_Lean_Syntax_node2(x_12, x_24, x_26, x_31);
lean_inc(x_12);
x_33 = l_Lean_Syntax_node1(x_12, x_23, x_32);
x_34 = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__25, &l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__25_once, _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__25);
x_35 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__26));
lean_inc(x_9);
lean_inc(x_8);
x_36 = l_Lean_addMacroScope(x_8, x_35, x_9);
lean_inc(x_12);
x_37 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_37, 0, x_12);
lean_ctor_set(x_37, 1, x_34);
lean_ctor_set(x_37, 2, x_36);
lean_ctor_set(x_37, 3, x_30);
lean_inc(x_12);
x_38 = l_Lean_Syntax_node2(x_12, x_24, x_26, x_37);
lean_inc(x_12);
x_39 = l_Lean_Syntax_node1(x_12, x_23, x_38);
lean_inc(x_12);
x_40 = l_Lean_Syntax_node2(x_12, x_18, x_33, x_39);
lean_inc(x_12);
x_41 = l_Lean_Syntax_node1(x_12, x_22, x_40);
x_42 = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__27, &l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__27_once, _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__27);
lean_inc(x_12);
x_43 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_43, 0, x_12);
lean_ctor_set(x_43, 1, x_18);
lean_ctor_set(x_43, 2, x_42);
x_44 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__28));
lean_inc(x_12);
x_45 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_45, 0, x_12);
lean_ctor_set(x_45, 1, x_44);
x_46 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__30));
x_47 = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__32, &l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__32_once, _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__32);
x_48 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__33));
lean_inc(x_9);
lean_inc(x_8);
x_49 = l_Lean_addMacroScope(x_8, x_48, x_9);
x_50 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__35));
lean_inc(x_12);
x_51 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_51, 0, x_12);
lean_ctor_set(x_51, 1, x_47);
lean_ctor_set(x_51, 2, x_49);
lean_ctor_set(x_51, 3, x_50);
lean_inc_ref_n(x_43, 2);
lean_inc(x_12);
x_52 = l_Lean_Syntax_node3(x_12, x_46, x_43, x_43, x_51);
x_53 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__36));
lean_inc(x_12);
x_54 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_54, 0, x_12);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__38, &l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__38_once, _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__38);
x_56 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__39));
lean_inc(x_9);
lean_inc(x_8);
x_57 = l_Lean_addMacroScope(x_8, x_56, x_9);
x_58 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__43));
lean_inc(x_12);
x_59 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_59, 0, x_12);
lean_ctor_set(x_59, 1, x_55);
lean_ctor_set(x_59, 2, x_57);
lean_ctor_set(x_59, 3, x_58);
lean_inc_ref_n(x_43, 2);
lean_inc(x_12);
x_60 = l_Lean_Syntax_node3(x_12, x_46, x_43, x_43, x_59);
x_61 = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__45, &l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__45_once, _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__45);
x_62 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__48));
lean_inc(x_9);
lean_inc(x_8);
x_63 = l_Lean_addMacroScope(x_8, x_62, x_9);
x_64 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__52));
lean_inc(x_12);
x_65 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_65, 0, x_12);
lean_ctor_set(x_65, 1, x_61);
lean_ctor_set(x_65, 2, x_63);
lean_ctor_set(x_65, 3, x_64);
lean_inc_ref_n(x_43, 2);
lean_inc(x_12);
x_66 = l_Lean_Syntax_node3(x_12, x_46, x_43, x_43, x_65);
x_67 = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__54, &l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__54_once, _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__54);
x_68 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__55));
lean_inc(x_9);
lean_inc(x_8);
x_69 = l_Lean_addMacroScope(x_8, x_68, x_9);
x_70 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__57));
lean_inc(x_12);
x_71 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_71, 0, x_12);
lean_ctor_set(x_71, 1, x_67);
lean_ctor_set(x_71, 2, x_69);
lean_ctor_set(x_71, 3, x_70);
lean_inc_ref_n(x_43, 2);
lean_inc(x_12);
x_72 = l_Lean_Syntax_node3(x_12, x_46, x_43, x_43, x_71);
x_73 = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__59, &l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__59_once, _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__59);
x_74 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__60));
lean_inc(x_9);
lean_inc(x_8);
x_75 = l_Lean_addMacroScope(x_8, x_74, x_9);
x_76 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__62));
lean_inc(x_12);
x_77 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_77, 0, x_12);
lean_ctor_set(x_77, 1, x_73);
lean_ctor_set(x_77, 2, x_75);
lean_ctor_set(x_77, 3, x_76);
lean_inc_ref_n(x_43, 2);
lean_inc(x_12);
x_78 = l_Lean_Syntax_node3(x_12, x_46, x_43, x_43, x_77);
x_79 = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__64, &l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__64_once, _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__64);
x_80 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__67));
lean_inc(x_9);
lean_inc(x_8);
x_81 = l_Lean_addMacroScope(x_8, x_80, x_9);
x_82 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__69));
lean_inc(x_12);
x_83 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_83, 0, x_12);
lean_ctor_set(x_83, 1, x_79);
lean_ctor_set(x_83, 2, x_81);
lean_ctor_set(x_83, 3, x_82);
lean_inc_ref_n(x_43, 2);
lean_inc(x_12);
x_84 = l_Lean_Syntax_node3(x_12, x_46, x_43, x_43, x_83);
x_85 = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__71, &l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__71_once, _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__71);
x_86 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__74));
x_87 = l_Lean_addMacroScope(x_8, x_86, x_9);
x_88 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__76));
lean_inc(x_12);
x_89 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_89, 0, x_12);
lean_ctor_set(x_89, 1, x_85);
lean_ctor_set(x_89, 2, x_87);
lean_ctor_set(x_89, 3, x_88);
lean_inc_ref_n(x_43, 2);
lean_inc(x_12);
x_90 = l_Lean_Syntax_node3(x_12, x_46, x_43, x_43, x_89);
x_91 = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__77, &l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__77_once, _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__77);
x_92 = lean_array_push(x_91, x_52);
lean_inc_ref(x_54);
x_93 = lean_array_push(x_92, x_54);
x_94 = lean_array_push(x_93, x_60);
lean_inc_ref(x_54);
x_95 = lean_array_push(x_94, x_54);
x_96 = lean_array_push(x_95, x_66);
lean_inc_ref(x_54);
x_97 = lean_array_push(x_96, x_54);
x_98 = lean_array_push(x_97, x_72);
lean_inc_ref(x_54);
x_99 = lean_array_push(x_98, x_54);
x_100 = lean_array_push(x_99, x_78);
lean_inc_ref(x_54);
x_101 = lean_array_push(x_100, x_54);
x_102 = lean_array_push(x_101, x_84);
x_103 = lean_array_push(x_102, x_54);
x_104 = lean_array_push(x_103, x_90);
lean_inc(x_12);
x_105 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_105, 0, x_12);
lean_ctor_set(x_105, 1, x_18);
lean_ctor_set(x_105, 2, x_104);
x_106 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__78));
lean_inc(x_12);
x_107 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_107, 0, x_12);
lean_ctor_set(x_107, 1, x_106);
lean_inc(x_12);
x_108 = l_Lean_Syntax_node3(x_12, x_18, x_45, x_105, x_107);
lean_inc_ref_n(x_43, 2);
lean_inc(x_12);
x_109 = l_Lean_Syntax_node6(x_12, x_20, x_21, x_41, x_43, x_43, x_108, x_43);
lean_inc(x_12);
x_110 = l_Lean_Syntax_node1(x_12, x_18, x_109);
lean_inc(x_12);
x_111 = l_Lean_Syntax_node1(x_12, x_17, x_110);
lean_inc(x_12);
x_112 = l_Lean_Syntax_node1(x_12, x_16, x_111);
x_113 = l_Lean_Syntax_node2(x_12, x_13, x_15, x_112);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_3);
return x_114;
}
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__3));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__7));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__13(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__12));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__15(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(17u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticClean__wf__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = ((lean_object*)(l_tacticClean__wf___closed__1));
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec_ref(x_2);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 5);
lean_inc(x_10);
lean_dec_ref(x_2);
x_11 = 0;
x_12 = l_Lean_SourceInfo_fromRef(x_10, x_11);
lean_dec(x_10);
x_13 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__12));
x_14 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__13));
lean_inc(x_12);
x_15 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_13);
x_16 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__15));
x_17 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__11));
x_18 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__17));
x_19 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__19));
x_20 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__20));
lean_inc(x_12);
x_21 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_21, 0, x_12);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__22, &l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__22_once, _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__22);
x_23 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__23));
lean_inc(x_9);
lean_inc(x_8);
x_24 = l_Lean_addMacroScope(x_8, x_23, x_9);
x_25 = lean_box(0);
lean_inc(x_12);
x_26 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_26, 0, x_12);
lean_ctor_set(x_26, 1, x_22);
lean_ctor_set(x_26, 2, x_24);
lean_ctor_set(x_26, 3, x_25);
lean_inc_ref(x_21);
lean_inc(x_12);
x_27 = l_Lean_Syntax_node2(x_12, x_19, x_21, x_26);
lean_inc(x_12);
x_28 = l_Lean_Syntax_node1(x_12, x_18, x_27);
x_29 = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__25, &l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__25_once, _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__25);
x_30 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__26));
lean_inc(x_9);
lean_inc(x_8);
x_31 = l_Lean_addMacroScope(x_8, x_30, x_9);
lean_inc(x_12);
x_32 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_32, 0, x_12);
lean_ctor_set(x_32, 1, x_29);
lean_ctor_set(x_32, 2, x_31);
lean_ctor_set(x_32, 3, x_25);
lean_inc(x_12);
x_33 = l_Lean_Syntax_node2(x_12, x_19, x_21, x_32);
lean_inc(x_12);
x_34 = l_Lean_Syntax_node1(x_12, x_18, x_33);
x_35 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__1));
x_36 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__2));
lean_inc(x_12);
x_37 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_37, 0, x_12);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__4, &l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__4_once, _init_l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__4);
x_39 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__5));
lean_inc(x_9);
lean_inc(x_8);
x_40 = l_Lean_addMacroScope(x_8, x_39, x_9);
lean_inc(x_12);
x_41 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_41, 0, x_12);
lean_ctor_set(x_41, 1, x_38);
lean_ctor_set(x_41, 2, x_40);
lean_ctor_set(x_41, 3, x_25);
lean_inc(x_12);
x_42 = l_Lean_Syntax_node2(x_12, x_35, x_37, x_41);
lean_inc(x_12);
x_43 = l_Lean_Syntax_node1(x_12, x_18, x_42);
lean_inc(x_12);
x_44 = l_Lean_Syntax_node3(x_12, x_17, x_28, x_34, x_43);
lean_inc(x_12);
x_45 = l_Lean_Syntax_node1(x_12, x_16, x_44);
x_46 = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__27, &l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__27_once, _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__27);
lean_inc(x_12);
x_47 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_47, 0, x_12);
lean_ctor_set(x_47, 1, x_17);
lean_ctor_set(x_47, 2, x_46);
x_48 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__6));
lean_inc(x_12);
x_49 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_49, 0, x_12);
lean_ctor_set(x_49, 1, x_48);
lean_inc(x_12);
x_50 = l_Lean_Syntax_node1(x_12, x_17, x_49);
x_51 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__28));
lean_inc(x_12);
x_52 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_52, 0, x_12);
lean_ctor_set(x_52, 1, x_51);
x_53 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__30));
x_54 = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__32, &l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__32_once, _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__32);
x_55 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__33));
lean_inc(x_9);
lean_inc(x_8);
x_56 = l_Lean_addMacroScope(x_8, x_55, x_9);
x_57 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__35));
lean_inc(x_12);
x_58 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_58, 0, x_12);
lean_ctor_set(x_58, 1, x_54);
lean_ctor_set(x_58, 2, x_56);
lean_ctor_set(x_58, 3, x_57);
lean_inc_ref_n(x_47, 2);
lean_inc(x_12);
x_59 = l_Lean_Syntax_node3(x_12, x_53, x_47, x_47, x_58);
x_60 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__36));
lean_inc(x_12);
x_61 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_61, 0, x_12);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__38, &l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__38_once, _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__38);
x_63 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__39));
lean_inc(x_9);
lean_inc(x_8);
x_64 = l_Lean_addMacroScope(x_8, x_63, x_9);
x_65 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__43));
lean_inc(x_12);
x_66 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_66, 0, x_12);
lean_ctor_set(x_66, 1, x_62);
lean_ctor_set(x_66, 2, x_64);
lean_ctor_set(x_66, 3, x_65);
lean_inc_ref_n(x_47, 2);
lean_inc(x_12);
x_67 = l_Lean_Syntax_node3(x_12, x_53, x_47, x_47, x_66);
x_68 = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__45, &l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__45_once, _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__45);
x_69 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__48));
lean_inc(x_9);
lean_inc(x_8);
x_70 = l_Lean_addMacroScope(x_8, x_69, x_9);
x_71 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__52));
lean_inc(x_12);
x_72 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_72, 0, x_12);
lean_ctor_set(x_72, 1, x_68);
lean_ctor_set(x_72, 2, x_70);
lean_ctor_set(x_72, 3, x_71);
lean_inc_ref_n(x_47, 2);
lean_inc(x_12);
x_73 = l_Lean_Syntax_node3(x_12, x_53, x_47, x_47, x_72);
x_74 = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__54, &l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__54_once, _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__54);
x_75 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__55));
lean_inc(x_9);
lean_inc(x_8);
x_76 = l_Lean_addMacroScope(x_8, x_75, x_9);
x_77 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__57));
lean_inc(x_12);
x_78 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_78, 0, x_12);
lean_ctor_set(x_78, 1, x_74);
lean_ctor_set(x_78, 2, x_76);
lean_ctor_set(x_78, 3, x_77);
lean_inc_ref_n(x_47, 2);
lean_inc(x_12);
x_79 = l_Lean_Syntax_node3(x_12, x_53, x_47, x_47, x_78);
x_80 = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__59, &l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__59_once, _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__59);
x_81 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__60));
lean_inc(x_9);
lean_inc(x_8);
x_82 = l_Lean_addMacroScope(x_8, x_81, x_9);
x_83 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__62));
lean_inc(x_12);
x_84 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_84, 0, x_12);
lean_ctor_set(x_84, 1, x_80);
lean_ctor_set(x_84, 2, x_82);
lean_ctor_set(x_84, 3, x_83);
lean_inc_ref_n(x_47, 2);
lean_inc(x_12);
x_85 = l_Lean_Syntax_node3(x_12, x_53, x_47, x_47, x_84);
x_86 = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__64, &l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__64_once, _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__64);
x_87 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__67));
lean_inc(x_9);
lean_inc(x_8);
x_88 = l_Lean_addMacroScope(x_8, x_87, x_9);
x_89 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__69));
lean_inc(x_12);
x_90 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_90, 0, x_12);
lean_ctor_set(x_90, 1, x_86);
lean_ctor_set(x_90, 2, x_88);
lean_ctor_set(x_90, 3, x_89);
lean_inc_ref_n(x_47, 2);
lean_inc(x_12);
x_91 = l_Lean_Syntax_node3(x_12, x_53, x_47, x_47, x_90);
x_92 = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__71, &l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__71_once, _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__71);
x_93 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__74));
lean_inc(x_9);
lean_inc(x_8);
x_94 = l_Lean_addMacroScope(x_8, x_93, x_9);
x_95 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__76));
lean_inc(x_12);
x_96 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_96, 0, x_12);
lean_ctor_set(x_96, 1, x_92);
lean_ctor_set(x_96, 2, x_94);
lean_ctor_set(x_96, 3, x_95);
lean_inc_ref_n(x_47, 2);
lean_inc(x_12);
x_97 = l_Lean_Syntax_node3(x_12, x_53, x_47, x_47, x_96);
x_98 = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__8, &l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__8_once, _init_l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__8);
x_99 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__9));
lean_inc(x_9);
lean_inc(x_8);
x_100 = l_Lean_addMacroScope(x_8, x_99, x_9);
x_101 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__11));
lean_inc(x_12);
x_102 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_102, 0, x_12);
lean_ctor_set(x_102, 1, x_98);
lean_ctor_set(x_102, 2, x_100);
lean_ctor_set(x_102, 3, x_101);
lean_inc_ref_n(x_47, 2);
lean_inc(x_12);
x_103 = l_Lean_Syntax_node3(x_12, x_53, x_47, x_47, x_102);
x_104 = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__13, &l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__13_once, _init_l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__13);
x_105 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__14));
x_106 = l_Lean_addMacroScope(x_8, x_105, x_9);
lean_inc(x_12);
x_107 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_107, 0, x_12);
lean_ctor_set(x_107, 1, x_104);
lean_ctor_set(x_107, 2, x_106);
lean_ctor_set(x_107, 3, x_25);
lean_inc_ref_n(x_47, 2);
lean_inc(x_12);
x_108 = l_Lean_Syntax_node3(x_12, x_53, x_47, x_47, x_107);
x_109 = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__15, &l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__15_once, _init_l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__15);
x_110 = lean_array_push(x_109, x_59);
lean_inc_ref(x_61);
x_111 = lean_array_push(x_110, x_61);
x_112 = lean_array_push(x_111, x_67);
lean_inc_ref(x_61);
x_113 = lean_array_push(x_112, x_61);
x_114 = lean_array_push(x_113, x_73);
lean_inc_ref(x_61);
x_115 = lean_array_push(x_114, x_61);
x_116 = lean_array_push(x_115, x_79);
lean_inc_ref(x_61);
x_117 = lean_array_push(x_116, x_61);
x_118 = lean_array_push(x_117, x_85);
lean_inc_ref(x_61);
x_119 = lean_array_push(x_118, x_61);
x_120 = lean_array_push(x_119, x_91);
lean_inc_ref(x_61);
x_121 = lean_array_push(x_120, x_61);
x_122 = lean_array_push(x_121, x_97);
lean_inc_ref(x_61);
x_123 = lean_array_push(x_122, x_61);
x_124 = lean_array_push(x_123, x_103);
x_125 = lean_array_push(x_124, x_61);
x_126 = lean_array_push(x_125, x_108);
lean_inc(x_12);
x_127 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_127, 0, x_12);
lean_ctor_set(x_127, 1, x_17);
lean_ctor_set(x_127, 2, x_126);
x_128 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__78));
lean_inc(x_12);
x_129 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_129, 0, x_12);
lean_ctor_set(x_129, 1, x_128);
lean_inc(x_12);
x_130 = l_Lean_Syntax_node3(x_12, x_17, x_52, x_127, x_129);
lean_inc_ref(x_47);
x_131 = l_Lean_Syntax_node6(x_12, x_14, x_15, x_45, x_47, x_50, x_130, x_47);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_3);
return x_132;
}
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__5));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = ((lean_object*)(l_tacticDecreasing__trivial___closed__1));
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec_ref(x_2);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 5);
lean_inc(x_10);
lean_dec_ref(x_2);
x_11 = 0;
x_12 = l_Lean_SourceInfo_fromRef(x_10, x_11);
lean_dec(x_10);
x_13 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__1));
x_14 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__3));
x_15 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__4));
lean_inc(x_12);
x_16 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_15);
x_17 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__7));
x_18 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__9));
x_19 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__11));
x_20 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__12));
x_21 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__13));
lean_inc(x_12);
x_22 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_22, 0, x_12);
lean_ctor_set(x_22, 1, x_20);
x_23 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__15));
x_24 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__17));
x_25 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__19));
x_26 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__20));
lean_inc(x_12);
x_27 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_27, 0, x_12);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__6, &l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__6_once, _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__6);
x_29 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__7));
lean_inc(x_9);
lean_inc(x_8);
x_30 = l_Lean_addMacroScope(x_8, x_29, x_9);
x_31 = lean_box(0);
lean_inc(x_12);
x_32 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_32, 0, x_12);
lean_ctor_set(x_32, 1, x_28);
lean_ctor_set(x_32, 2, x_30);
lean_ctor_set(x_32, 3, x_31);
lean_inc(x_12);
x_33 = l_Lean_Syntax_node2(x_12, x_25, x_27, x_32);
lean_inc(x_12);
x_34 = l_Lean_Syntax_node1(x_12, x_24, x_33);
x_35 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__1));
x_36 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__2));
lean_inc(x_12);
x_37 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_37, 0, x_12);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__4, &l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__4_once, _init_l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__4);
x_39 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__5));
x_40 = l_Lean_addMacroScope(x_8, x_39, x_9);
lean_inc(x_12);
x_41 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_41, 0, x_12);
lean_ctor_set(x_41, 1, x_38);
lean_ctor_set(x_41, 2, x_40);
lean_ctor_set(x_41, 3, x_31);
lean_inc(x_12);
x_42 = l_Lean_Syntax_node2(x_12, x_35, x_37, x_41);
lean_inc(x_12);
x_43 = l_Lean_Syntax_node1(x_12, x_24, x_42);
lean_inc(x_12);
x_44 = l_Lean_Syntax_node2(x_12, x_19, x_34, x_43);
lean_inc(x_12);
x_45 = l_Lean_Syntax_node1(x_12, x_23, x_44);
x_46 = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__27, &l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__27_once, _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__27);
lean_inc(x_12);
x_47 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_47, 0, x_12);
lean_ctor_set(x_47, 1, x_19);
lean_ctor_set(x_47, 2, x_46);
lean_inc_ref_n(x_47, 3);
lean_inc(x_12);
x_48 = l_Lean_Syntax_node6(x_12, x_21, x_22, x_45, x_47, x_47, x_47, x_47);
lean_inc(x_12);
x_49 = l_Lean_Syntax_node1(x_12, x_19, x_48);
lean_inc(x_12);
x_50 = l_Lean_Syntax_node1(x_12, x_18, x_49);
lean_inc(x_12);
x_51 = l_Lean_Syntax_node1(x_12, x_17, x_50);
x_52 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__8));
lean_inc(x_12);
x_53 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_53, 0, x_12);
lean_ctor_set(x_53, 1, x_52);
lean_inc(x_12);
x_54 = l_Lean_Syntax_node3(x_12, x_14, x_16, x_51, x_53);
x_55 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__9));
lean_inc(x_12);
x_56 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_56, 0, x_12);
lean_ctor_set(x_56, 1, x_55);
x_57 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__10));
x_58 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__11));
lean_inc(x_12);
x_59 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_59, 0, x_12);
lean_ctor_set(x_59, 1, x_57);
lean_inc(x_12);
x_60 = l_Lean_Syntax_node1(x_12, x_58, x_59);
x_61 = l_Lean_Syntax_node3(x_12, x_13, x_54, x_56, x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_3);
return x_62;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = ((lean_object*)(l_tacticDecreasing__trivial___closed__1));
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_8 = lean_ctor_get(x_2, 5);
x_9 = 0;
x_10 = l_Lean_SourceInfo_fromRef(x_8, x_9);
x_11 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__2___closed__0));
x_12 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__2___closed__1));
lean_inc(x_10);
x_13 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_11);
x_14 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__15));
x_15 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__11));
x_16 = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__27, &l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__27_once, _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__27);
lean_inc(x_10);
x_17 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set(x_17, 2, x_16);
lean_inc(x_10);
x_18 = l_Lean_Syntax_node1(x_10, x_14, x_17);
x_19 = l_Lean_Syntax_node2(x_10, x_12, x_13, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_3);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__2(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = ((lean_object*)(l_tacticDecreasing__trivial___closed__1));
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_2, 5);
x_9 = 0;
x_10 = l_Lean_SourceInfo_fromRef(x_8, x_9);
x_11 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___closed__0));
x_12 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___closed__1));
lean_inc(x_10);
x_13 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_Lean_Syntax_node1(x_10, x_12, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_3);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__4));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = ((lean_object*)(l_tacticDecreasing__trivial__pre__omega___closed__1));
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec_ref(x_2);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 5);
lean_inc(x_10);
lean_dec_ref(x_2);
x_11 = 0;
x_12 = l_Lean_SourceInfo_fromRef(x_10, x_11);
lean_dec(x_10);
x_13 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__1));
x_14 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__11));
x_15 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__2));
x_16 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__3));
lean_inc(x_12);
x_17 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__5, &l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__5_once, _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__5);
x_19 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__7));
x_20 = l_Lean_addMacroScope(x_8, x_19, x_9);
x_21 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__9));
lean_inc(x_12);
x_22 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_22, 0, x_12);
lean_ctor_set(x_22, 1, x_18);
lean_ctor_set(x_22, 2, x_20);
lean_ctor_set(x_22, 3, x_21);
lean_inc(x_12);
x_23 = l_Lean_Syntax_node2(x_12, x_16, x_17, x_22);
x_24 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__10));
lean_inc(x_12);
x_25 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_25, 0, x_12);
lean_ctor_set(x_25, 1, x_24);
x_26 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___closed__0));
x_27 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___closed__1));
lean_inc(x_12);
x_28 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_28, 0, x_12);
lean_ctor_set(x_28, 1, x_26);
lean_inc(x_12);
x_29 = l_Lean_Syntax_node1(x_12, x_27, x_28);
lean_inc(x_12);
x_30 = l_Lean_Syntax_node3(x_12, x_14, x_23, x_25, x_29);
x_31 = l_Lean_Syntax_node1(x_12, x_13, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_3);
return x_32;
}
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__0));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = ((lean_object*)(l_tacticDecreasing__trivial__pre__omega___closed__1));
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec_ref(x_2);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 5);
lean_inc(x_10);
lean_dec_ref(x_2);
x_11 = 0;
x_12 = l_Lean_SourceInfo_fromRef(x_10, x_11);
lean_dec(x_10);
x_13 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__1));
x_14 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__11));
x_15 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__2));
x_16 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__3));
lean_inc(x_12);
x_17 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__1, &l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__1_once, _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__1);
x_19 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__3));
x_20 = l_Lean_addMacroScope(x_8, x_19, x_9);
x_21 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__5));
lean_inc(x_12);
x_22 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_22, 0, x_12);
lean_ctor_set(x_22, 1, x_18);
lean_ctor_set(x_22, 2, x_20);
lean_ctor_set(x_22, 3, x_21);
lean_inc(x_12);
x_23 = l_Lean_Syntax_node2(x_12, x_16, x_17, x_22);
x_24 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__10));
lean_inc(x_12);
x_25 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_25, 0, x_12);
lean_ctor_set(x_25, 1, x_24);
x_26 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___closed__0));
x_27 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___closed__1));
lean_inc(x_12);
x_28 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_28, 0, x_12);
lean_ctor_set(x_28, 1, x_26);
lean_inc(x_12);
x_29 = l_Lean_Syntax_node1(x_12, x_27, x_28);
lean_inc(x_12);
x_30 = l_Lean_Syntax_node3(x_12, x_14, x_23, x_25, x_29);
x_31 = l_Lean_Syntax_node1(x_12, x_13, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_3);
return x_32;
}
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__0));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = ((lean_object*)(l_tacticDecreasing__trivial__pre__omega___closed__1));
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec_ref(x_2);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 5);
lean_inc(x_10);
lean_dec_ref(x_2);
x_11 = 0;
x_12 = l_Lean_SourceInfo_fromRef(x_10, x_11);
lean_dec(x_10);
x_13 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__1));
x_14 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__11));
x_15 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__2));
x_16 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__3));
lean_inc(x_12);
x_17 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__1, &l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__1_once, _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__1);
x_19 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__3));
x_20 = l_Lean_addMacroScope(x_8, x_19, x_9);
x_21 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__5));
lean_inc(x_12);
x_22 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_22, 0, x_12);
lean_ctor_set(x_22, 1, x_18);
lean_ctor_set(x_22, 2, x_20);
lean_ctor_set(x_22, 3, x_21);
lean_inc(x_12);
x_23 = l_Lean_Syntax_node2(x_12, x_16, x_17, x_22);
x_24 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__10));
lean_inc(x_12);
x_25 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_25, 0, x_12);
lean_ctor_set(x_25, 1, x_24);
x_26 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___closed__0));
x_27 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___closed__1));
lean_inc(x_12);
x_28 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_28, 0, x_12);
lean_ctor_set(x_28, 1, x_26);
lean_inc(x_12);
x_29 = l_Lean_Syntax_node1(x_12, x_27, x_28);
lean_inc(x_12);
x_30 = l_Lean_Syntax_node3(x_12, x_14, x_23, x_25, x_29);
x_31 = l_Lean_Syntax_node1(x_12, x_13, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_3);
return x_32;
}
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__9(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__8));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__16(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__15));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__22(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__21));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__28(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__27));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__37(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(9u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = ((lean_object*)(l_tacticDecreasing__with___00__closed__1));
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 5);
lean_inc(x_10);
lean_dec_ref(x_2);
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
lean_dec(x_1);
x_13 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__7));
x_14 = 0;
x_15 = l_Lean_SourceInfo_fromRef(x_10, x_14);
lean_dec(x_10);
x_16 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__3));
x_17 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__4));
lean_inc(x_15);
x_18 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
x_19 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__9));
x_20 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__11));
x_21 = ((lean_object*)(l_tacticClean__wf___closed__1));
x_22 = ((lean_object*)(l_tacticClean__wf___closed__2));
lean_inc(x_15);
x_23 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_23, 0, x_15);
lean_ctor_set(x_23, 1, x_22);
lean_inc(x_15);
x_24 = l_Lean_Syntax_node1(x_15, x_21, x_23);
x_25 = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__27, &l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__27_once, _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__27);
lean_inc(x_15);
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_15);
lean_ctor_set(x_26, 1, x_20);
lean_ctor_set(x_26, 2, x_25);
x_27 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__4));
x_28 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__5));
lean_inc(x_15);
x_29 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_29, 0, x_15);
lean_ctor_set(x_29, 1, x_28);
x_30 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__12));
x_31 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__13));
lean_inc(x_15);
x_32 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_32, 0, x_15);
lean_ctor_set(x_32, 1, x_30);
x_33 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__15));
lean_inc_ref(x_26);
lean_inc(x_15);
x_34 = l_Lean_Syntax_node1(x_15, x_33, x_26);
lean_inc_ref_n(x_26, 4);
lean_inc(x_15);
x_35 = l_Lean_Syntax_node6(x_15, x_31, x_32, x_34, x_26, x_26, x_26, x_26);
lean_inc(x_15);
x_36 = l_Lean_Syntax_node1(x_15, x_20, x_35);
lean_inc(x_15);
x_37 = l_Lean_Syntax_node1(x_15, x_19, x_36);
lean_inc(x_15);
x_38 = l_Lean_Syntax_node1(x_15, x_13, x_37);
lean_inc(x_15);
x_39 = l_Lean_Syntax_node2(x_15, x_27, x_29, x_38);
x_40 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__1));
x_41 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__2));
lean_inc(x_15);
x_42 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_42, 0, x_15);
lean_ctor_set(x_42, 1, x_41);
x_43 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__3));
x_44 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__4));
lean_inc(x_15);
x_45 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_45, 0, x_15);
lean_ctor_set(x_45, 1, x_43);
x_46 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__6));
x_47 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__7));
lean_inc(x_15);
x_48 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_48, 0, x_15);
lean_ctor_set(x_48, 1, x_47);
x_49 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__2));
x_50 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__3));
lean_inc(x_15);
x_51 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_51, 0, x_15);
lean_ctor_set(x_51, 1, x_49);
x_52 = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__9, &l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__9_once, _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__9);
x_53 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__12));
lean_inc(x_9);
lean_inc(x_8);
x_54 = l_Lean_addMacroScope(x_8, x_53, x_9);
x_55 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__14));
lean_inc(x_15);
x_56 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_56, 0, x_15);
lean_ctor_set(x_56, 1, x_52);
lean_ctor_set(x_56, 2, x_54);
lean_ctor_set(x_56, 3, x_55);
lean_inc_ref(x_51);
lean_inc(x_15);
x_57 = l_Lean_Syntax_node2(x_15, x_50, x_51, x_56);
lean_inc(x_15);
x_58 = l_Lean_Syntax_node1(x_15, x_20, x_57);
lean_inc(x_15);
x_59 = l_Lean_Syntax_node1(x_15, x_19, x_58);
lean_inc(x_15);
x_60 = l_Lean_Syntax_node1(x_15, x_13, x_59);
lean_inc_ref(x_48);
lean_inc(x_15);
x_61 = l_Lean_Syntax_node2(x_15, x_46, x_48, x_60);
x_62 = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__16, &l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__16_once, _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__16);
x_63 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__18));
lean_inc(x_9);
lean_inc(x_8);
x_64 = l_Lean_addMacroScope(x_8, x_63, x_9);
x_65 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__20));
lean_inc(x_15);
x_66 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_66, 0, x_15);
lean_ctor_set(x_66, 1, x_62);
lean_ctor_set(x_66, 2, x_64);
lean_ctor_set(x_66, 3, x_65);
lean_inc_ref(x_51);
lean_inc(x_15);
x_67 = l_Lean_Syntax_node2(x_15, x_50, x_51, x_66);
lean_inc(x_15);
x_68 = l_Lean_Syntax_node1(x_15, x_20, x_67);
lean_inc(x_15);
x_69 = l_Lean_Syntax_node1(x_15, x_19, x_68);
lean_inc(x_15);
x_70 = l_Lean_Syntax_node1(x_15, x_13, x_69);
lean_inc_ref(x_48);
lean_inc(x_15);
x_71 = l_Lean_Syntax_node2(x_15, x_46, x_48, x_70);
lean_inc(x_15);
x_72 = l_Lean_Syntax_node2(x_15, x_20, x_61, x_71);
lean_inc_ref(x_45);
lean_inc(x_15);
x_73 = l_Lean_Syntax_node2(x_15, x_44, x_45, x_72);
lean_inc(x_15);
x_74 = l_Lean_Syntax_node1(x_15, x_20, x_73);
lean_inc(x_15);
x_75 = l_Lean_Syntax_node1(x_15, x_19, x_74);
lean_inc(x_15);
x_76 = l_Lean_Syntax_node1(x_15, x_13, x_75);
x_77 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__8));
lean_inc(x_15);
x_78 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_78, 0, x_15);
lean_ctor_set(x_78, 1, x_77);
lean_inc_ref(x_78);
lean_inc_ref(x_18);
lean_inc(x_15);
x_79 = l_Lean_Syntax_node3(x_15, x_16, x_18, x_76, x_78);
lean_inc(x_15);
x_80 = l_Lean_Syntax_node1(x_15, x_20, x_79);
lean_inc(x_15);
x_81 = l_Lean_Syntax_node1(x_15, x_19, x_80);
lean_inc(x_15);
x_82 = l_Lean_Syntax_node1(x_15, x_13, x_81);
lean_inc_ref(x_42);
lean_inc(x_15);
x_83 = l_Lean_Syntax_node2(x_15, x_40, x_42, x_82);
x_84 = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__22, &l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__22_once, _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__22);
x_85 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__24));
lean_inc(x_9);
lean_inc(x_8);
x_86 = l_Lean_addMacroScope(x_8, x_85, x_9);
x_87 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__26));
lean_inc(x_15);
x_88 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_88, 0, x_15);
lean_ctor_set(x_88, 1, x_84);
lean_ctor_set(x_88, 2, x_86);
lean_ctor_set(x_88, 3, x_87);
lean_inc_ref(x_51);
lean_inc(x_15);
x_89 = l_Lean_Syntax_node2(x_15, x_50, x_51, x_88);
lean_inc(x_15);
x_90 = l_Lean_Syntax_node1(x_15, x_20, x_89);
lean_inc(x_15);
x_91 = l_Lean_Syntax_node1(x_15, x_19, x_90);
lean_inc(x_15);
x_92 = l_Lean_Syntax_node1(x_15, x_13, x_91);
lean_inc_ref(x_48);
lean_inc(x_15);
x_93 = l_Lean_Syntax_node2(x_15, x_46, x_48, x_92);
x_94 = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__28, &l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__28_once, _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__28);
x_95 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__29));
x_96 = l_Lean_addMacroScope(x_8, x_95, x_9);
x_97 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__31));
lean_inc(x_15);
x_98 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_98, 0, x_15);
lean_ctor_set(x_98, 1, x_94);
lean_ctor_set(x_98, 2, x_96);
lean_ctor_set(x_98, 3, x_97);
lean_inc(x_15);
x_99 = l_Lean_Syntax_node2(x_15, x_50, x_51, x_98);
lean_inc(x_15);
x_100 = l_Lean_Syntax_node1(x_15, x_20, x_99);
lean_inc(x_15);
x_101 = l_Lean_Syntax_node1(x_15, x_19, x_100);
lean_inc(x_15);
x_102 = l_Lean_Syntax_node1(x_15, x_13, x_101);
lean_inc_ref(x_48);
lean_inc(x_15);
x_103 = l_Lean_Syntax_node2(x_15, x_46, x_48, x_102);
lean_inc(x_15);
x_104 = l_Lean_Syntax_node2(x_15, x_20, x_93, x_103);
lean_inc_ref(x_45);
lean_inc(x_15);
x_105 = l_Lean_Syntax_node2(x_15, x_44, x_45, x_104);
lean_inc(x_15);
x_106 = l_Lean_Syntax_node1(x_15, x_20, x_105);
lean_inc(x_15);
x_107 = l_Lean_Syntax_node1(x_15, x_19, x_106);
lean_inc(x_15);
x_108 = l_Lean_Syntax_node1(x_15, x_13, x_107);
lean_inc_ref(x_78);
lean_inc_ref(x_18);
lean_inc(x_15);
x_109 = l_Lean_Syntax_node3(x_15, x_16, x_18, x_108, x_78);
lean_inc(x_15);
x_110 = l_Lean_Syntax_node1(x_15, x_20, x_109);
lean_inc(x_15);
x_111 = l_Lean_Syntax_node1(x_15, x_19, x_110);
lean_inc(x_15);
x_112 = l_Lean_Syntax_node1(x_15, x_13, x_111);
lean_inc(x_15);
x_113 = l_Lean_Syntax_node2(x_15, x_40, x_42, x_112);
x_114 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__10));
x_115 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__11));
lean_inc(x_15);
x_116 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_116, 0, x_15);
lean_ctor_set(x_116, 1, x_114);
lean_inc(x_15);
x_117 = l_Lean_Syntax_node1(x_15, x_115, x_116);
lean_inc(x_15);
x_118 = l_Lean_Syntax_node1(x_15, x_20, x_117);
lean_inc(x_15);
x_119 = l_Lean_Syntax_node1(x_15, x_19, x_118);
lean_inc(x_15);
x_120 = l_Lean_Syntax_node1(x_15, x_13, x_119);
lean_inc_ref(x_48);
lean_inc(x_15);
x_121 = l_Lean_Syntax_node2(x_15, x_46, x_48, x_120);
lean_inc_ref(x_48);
lean_inc(x_15);
x_122 = l_Lean_Syntax_node2(x_15, x_46, x_48, x_12);
x_123 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__32));
x_124 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__33));
lean_inc(x_15);
x_125 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_125, 0, x_15);
lean_ctor_set(x_125, 1, x_123);
x_126 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__35));
x_127 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__36));
lean_inc(x_15);
x_128 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_128, 0, x_15);
lean_ctor_set(x_128, 1, x_127);
lean_inc(x_15);
x_129 = l_Lean_Syntax_node1(x_15, x_126, x_128);
lean_inc(x_15);
x_130 = l_Lean_Syntax_node1(x_15, x_20, x_129);
lean_inc(x_15);
x_131 = l_Lean_Syntax_node2(x_15, x_124, x_125, x_130);
lean_inc(x_15);
x_132 = l_Lean_Syntax_node1(x_15, x_20, x_131);
lean_inc(x_15);
x_133 = l_Lean_Syntax_node1(x_15, x_19, x_132);
lean_inc(x_15);
x_134 = l_Lean_Syntax_node1(x_15, x_13, x_133);
lean_inc(x_15);
x_135 = l_Lean_Syntax_node2(x_15, x_46, x_48, x_134);
lean_inc(x_15);
x_136 = l_Lean_Syntax_node3(x_15, x_20, x_121, x_122, x_135);
lean_inc(x_15);
x_137 = l_Lean_Syntax_node2(x_15, x_44, x_45, x_136);
x_138 = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__37, &l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__37_once, _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__37);
x_139 = lean_array_push(x_138, x_24);
lean_inc_ref(x_26);
x_140 = lean_array_push(x_139, x_26);
x_141 = lean_array_push(x_140, x_39);
lean_inc_ref(x_26);
x_142 = lean_array_push(x_141, x_26);
x_143 = lean_array_push(x_142, x_83);
lean_inc_ref(x_26);
x_144 = lean_array_push(x_143, x_26);
x_145 = lean_array_push(x_144, x_113);
x_146 = lean_array_push(x_145, x_26);
x_147 = lean_array_push(x_146, x_137);
lean_inc(x_15);
x_148 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_148, 0, x_15);
lean_ctor_set(x_148, 1, x_20);
lean_ctor_set(x_148, 2, x_147);
lean_inc(x_15);
x_149 = l_Lean_Syntax_node1(x_15, x_19, x_148);
lean_inc(x_15);
x_150 = l_Lean_Syntax_node1(x_15, x_13, x_149);
x_151 = l_Lean_Syntax_node3(x_15, x_16, x_18, x_150, x_78);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_3);
return x_152;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = ((lean_object*)(l_tacticDecreasing__tactic___closed__1));
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_8 = lean_ctor_get(x_2, 5);
x_9 = 0;
x_10 = l_Lean_SourceInfo_fromRef(x_8, x_9);
x_11 = ((lean_object*)(l_tacticDecreasing__with___00__closed__1));
x_12 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___closed__0));
lean_inc(x_10);
x_13 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
x_14 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__7));
x_15 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__9));
x_16 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__11));
x_17 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__3));
x_18 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__4));
lean_inc(x_10);
x_19 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_19, 0, x_10);
lean_ctor_set(x_19, 1, x_17);
x_20 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__6));
x_21 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__7));
lean_inc(x_10);
x_22 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_22, 0, x_10);
lean_ctor_set(x_22, 1, x_21);
x_23 = ((lean_object*)(l_tacticDecreasing__trivial___closed__1));
x_24 = ((lean_object*)(l_tacticDecreasing__trivial___closed__2));
lean_inc(x_10);
x_25 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_25, 0, x_10);
lean_ctor_set(x_25, 1, x_24);
lean_inc(x_10);
x_26 = l_Lean_Syntax_node1(x_10, x_23, x_25);
lean_inc(x_26);
lean_inc(x_10);
x_27 = l_Lean_Syntax_node1(x_10, x_16, x_26);
lean_inc(x_10);
x_28 = l_Lean_Syntax_node1(x_10, x_15, x_27);
lean_inc(x_10);
x_29 = l_Lean_Syntax_node1(x_10, x_14, x_28);
lean_inc_ref(x_22);
lean_inc(x_10);
x_30 = l_Lean_Syntax_node2(x_10, x_20, x_22, x_29);
x_31 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___closed__2));
x_32 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___closed__3));
lean_inc(x_10);
x_33 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_33, 0, x_10);
lean_ctor_set(x_33, 1, x_32);
lean_inc(x_10);
x_34 = l_Lean_Syntax_node1(x_10, x_31, x_33);
x_35 = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__10));
lean_inc(x_10);
x_36 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_36, 0, x_10);
lean_ctor_set(x_36, 1, x_35);
lean_inc(x_10);
x_37 = l_Lean_Syntax_node3(x_10, x_16, x_34, x_36, x_26);
lean_inc(x_10);
x_38 = l_Lean_Syntax_node1(x_10, x_15, x_37);
lean_inc(x_10);
x_39 = l_Lean_Syntax_node1(x_10, x_14, x_38);
lean_inc(x_10);
x_40 = l_Lean_Syntax_node2(x_10, x_20, x_22, x_39);
lean_inc(x_10);
x_41 = l_Lean_Syntax_node2(x_10, x_16, x_30, x_40);
lean_inc(x_10);
x_42 = l_Lean_Syntax_node2(x_10, x_18, x_19, x_41);
lean_inc(x_10);
x_43 = l_Lean_Syntax_node1(x_10, x_16, x_42);
lean_inc(x_10);
x_44 = l_Lean_Syntax_node1(x_10, x_15, x_43);
lean_inc(x_10);
x_45 = l_Lean_Syntax_node1(x_10, x_14, x_44);
x_46 = l_Lean_Syntax_node2(x_10, x_11, x_13, x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_3);
return x_47;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
lean_object* initialize_Init_WF(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_WFTactics(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_WF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

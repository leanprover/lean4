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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
static const lean_string_object l_tacticSimp__wf___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "tacticSimp_wf"};
static const lean_object* l_tacticSimp__wf___closed__0 = (const lean_object*)&l_tacticSimp__wf___closed__0_value;
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
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__77 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__77_value;
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticClean__wf__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___boxed(lean_object*, lean_object*, lean_object*);
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
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__22(void){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_64_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__21));
v___x_65_ = l_String_toRawSubstring_x27(v___x_64_);
return v___x_65_;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__25(void){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_69_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__24));
v___x_70_ = l_String_toRawSubstring_x27(v___x_69_);
return v___x_70_;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__27(void){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = l_Array_mkArray0(lean_box(0));
return v___x_73_;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__32(void){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_82_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__31));
v___x_83_ = l_String_toRawSubstring_x27(v___x_82_);
return v___x_83_;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__38(void){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_94_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__37));
v___x_95_ = l_String_toRawSubstring_x27(v___x_94_);
return v___x_95_;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__45(void){
_start:
{
lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_110_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__44));
v___x_111_ = l_String_toRawSubstring_x27(v___x_110_);
return v___x_111_;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__54(void){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_129_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__53));
v___x_130_ = l_String_toRawSubstring_x27(v___x_129_);
return v___x_130_;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__59(void){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_140_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__58));
v___x_141_ = l_String_toRawSubstring_x27(v___x_140_);
return v___x_141_;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__64(void){
_start:
{
lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_151_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__63));
v___x_152_ = l_String_toRawSubstring_x27(v___x_151_);
return v___x_152_;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__71(void){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_165_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__70));
v___x_166_ = l_String_toRawSubstring_x27(v___x_165_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1(lean_object* v_x_179_, lean_object* v_a_180_, lean_object* v_a_181_){
_start:
{
lean_object* v___x_182_; uint8_t v___x_183_; 
v___x_182_ = ((lean_object*)(l_tacticSimp__wf___closed__1));
v___x_183_ = l_Lean_Syntax_isOfKind(v_x_179_, v___x_182_);
if (v___x_183_ == 0)
{
lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_184_ = lean_box(1);
v___x_185_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_185_, 0, v___x_184_);
lean_ctor_set(v___x_185_, 1, v_a_181_);
return v___x_185_;
}
else
{
lean_object* v_quotContext_186_; lean_object* v_currMacroScope_187_; lean_object* v_ref_188_; uint8_t v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v_quotContext_186_ = lean_ctor_get(v_a_180_, 1);
v_currMacroScope_187_ = lean_ctor_get(v_a_180_, 2);
v_ref_188_ = lean_ctor_get(v_a_180_, 5);
v___x_189_ = 0;
v___x_190_ = l_Lean_SourceInfo_fromRef(v_ref_188_, v___x_189_);
v___x_191_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__4));
v___x_192_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__5));
lean_inc_n(v___x_190_, 35);
v___x_193_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_193_, 0, v___x_190_);
lean_ctor_set(v___x_193_, 1, v___x_192_);
v___x_194_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__7));
v___x_195_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__9));
v___x_196_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__11));
v___x_197_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__12));
v___x_198_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__13));
v___x_199_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_199_, 0, v___x_190_);
lean_ctor_set(v___x_199_, 1, v___x_197_);
v___x_200_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__15));
v___x_201_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__17));
v___x_202_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__19));
v___x_203_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__20));
v___x_204_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_204_, 0, v___x_190_);
lean_ctor_set(v___x_204_, 1, v___x_203_);
v___x_205_ = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__22, &l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__22_once, _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__22);
v___x_206_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__23));
lean_inc_n(v_currMacroScope_187_, 9);
lean_inc_n(v_quotContext_186_, 9);
v___x_207_ = l_Lean_addMacroScope(v_quotContext_186_, v___x_206_, v_currMacroScope_187_);
v___x_208_ = lean_box(0);
v___x_209_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_209_, 0, v___x_190_);
lean_ctor_set(v___x_209_, 1, v___x_205_);
lean_ctor_set(v___x_209_, 2, v___x_207_);
lean_ctor_set(v___x_209_, 3, v___x_208_);
lean_inc_ref(v___x_204_);
v___x_210_ = l_Lean_Syntax_node2(v___x_190_, v___x_202_, v___x_204_, v___x_209_);
v___x_211_ = l_Lean_Syntax_node1(v___x_190_, v___x_201_, v___x_210_);
v___x_212_ = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__25, &l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__25_once, _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__25);
v___x_213_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__26));
v___x_214_ = l_Lean_addMacroScope(v_quotContext_186_, v___x_213_, v_currMacroScope_187_);
v___x_215_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_215_, 0, v___x_190_);
lean_ctor_set(v___x_215_, 1, v___x_212_);
lean_ctor_set(v___x_215_, 2, v___x_214_);
lean_ctor_set(v___x_215_, 3, v___x_208_);
v___x_216_ = l_Lean_Syntax_node2(v___x_190_, v___x_202_, v___x_204_, v___x_215_);
v___x_217_ = l_Lean_Syntax_node1(v___x_190_, v___x_201_, v___x_216_);
v___x_218_ = l_Lean_Syntax_node2(v___x_190_, v___x_196_, v___x_211_, v___x_217_);
v___x_219_ = l_Lean_Syntax_node1(v___x_190_, v___x_200_, v___x_218_);
v___x_220_ = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__27, &l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__27_once, _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__27);
v___x_221_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_221_, 0, v___x_190_);
lean_ctor_set(v___x_221_, 1, v___x_196_);
lean_ctor_set(v___x_221_, 2, v___x_220_);
v___x_222_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__28));
v___x_223_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_223_, 0, v___x_190_);
lean_ctor_set(v___x_223_, 1, v___x_222_);
v___x_224_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__30));
v___x_225_ = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__32, &l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__32_once, _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__32);
v___x_226_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__33));
v___x_227_ = l_Lean_addMacroScope(v_quotContext_186_, v___x_226_, v_currMacroScope_187_);
v___x_228_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__35));
v___x_229_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_229_, 0, v___x_190_);
lean_ctor_set(v___x_229_, 1, v___x_225_);
lean_ctor_set(v___x_229_, 2, v___x_227_);
lean_ctor_set(v___x_229_, 3, v___x_228_);
lean_inc_ref_n(v___x_221_, 16);
v___x_230_ = l_Lean_Syntax_node3(v___x_190_, v___x_224_, v___x_221_, v___x_221_, v___x_229_);
v___x_231_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__36));
v___x_232_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_232_, 0, v___x_190_);
lean_ctor_set(v___x_232_, 1, v___x_231_);
v___x_233_ = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__38, &l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__38_once, _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__38);
v___x_234_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__39));
v___x_235_ = l_Lean_addMacroScope(v_quotContext_186_, v___x_234_, v_currMacroScope_187_);
v___x_236_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__43));
v___x_237_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_237_, 0, v___x_190_);
lean_ctor_set(v___x_237_, 1, v___x_233_);
lean_ctor_set(v___x_237_, 2, v___x_235_);
lean_ctor_set(v___x_237_, 3, v___x_236_);
v___x_238_ = l_Lean_Syntax_node3(v___x_190_, v___x_224_, v___x_221_, v___x_221_, v___x_237_);
v___x_239_ = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__45, &l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__45_once, _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__45);
v___x_240_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__48));
v___x_241_ = l_Lean_addMacroScope(v_quotContext_186_, v___x_240_, v_currMacroScope_187_);
v___x_242_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__52));
v___x_243_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_243_, 0, v___x_190_);
lean_ctor_set(v___x_243_, 1, v___x_239_);
lean_ctor_set(v___x_243_, 2, v___x_241_);
lean_ctor_set(v___x_243_, 3, v___x_242_);
v___x_244_ = l_Lean_Syntax_node3(v___x_190_, v___x_224_, v___x_221_, v___x_221_, v___x_243_);
v___x_245_ = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__54, &l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__54_once, _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__54);
v___x_246_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__55));
v___x_247_ = l_Lean_addMacroScope(v_quotContext_186_, v___x_246_, v_currMacroScope_187_);
v___x_248_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__57));
v___x_249_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_249_, 0, v___x_190_);
lean_ctor_set(v___x_249_, 1, v___x_245_);
lean_ctor_set(v___x_249_, 2, v___x_247_);
lean_ctor_set(v___x_249_, 3, v___x_248_);
v___x_250_ = l_Lean_Syntax_node3(v___x_190_, v___x_224_, v___x_221_, v___x_221_, v___x_249_);
v___x_251_ = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__59, &l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__59_once, _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__59);
v___x_252_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__60));
v___x_253_ = l_Lean_addMacroScope(v_quotContext_186_, v___x_252_, v_currMacroScope_187_);
v___x_254_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__62));
v___x_255_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_255_, 0, v___x_190_);
lean_ctor_set(v___x_255_, 1, v___x_251_);
lean_ctor_set(v___x_255_, 2, v___x_253_);
lean_ctor_set(v___x_255_, 3, v___x_254_);
v___x_256_ = l_Lean_Syntax_node3(v___x_190_, v___x_224_, v___x_221_, v___x_221_, v___x_255_);
v___x_257_ = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__64, &l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__64_once, _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__64);
v___x_258_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__67));
v___x_259_ = l_Lean_addMacroScope(v_quotContext_186_, v___x_258_, v_currMacroScope_187_);
v___x_260_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__69));
v___x_261_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_261_, 0, v___x_190_);
lean_ctor_set(v___x_261_, 1, v___x_257_);
lean_ctor_set(v___x_261_, 2, v___x_259_);
lean_ctor_set(v___x_261_, 3, v___x_260_);
v___x_262_ = l_Lean_Syntax_node3(v___x_190_, v___x_224_, v___x_221_, v___x_221_, v___x_261_);
v___x_263_ = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__71, &l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__71_once, _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__71);
v___x_264_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__74));
v___x_265_ = l_Lean_addMacroScope(v_quotContext_186_, v___x_264_, v_currMacroScope_187_);
v___x_266_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__76));
v___x_267_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_267_, 0, v___x_190_);
lean_ctor_set(v___x_267_, 1, v___x_263_);
lean_ctor_set(v___x_267_, 2, v___x_265_);
lean_ctor_set(v___x_267_, 3, v___x_266_);
v___x_268_ = l_Lean_Syntax_node3(v___x_190_, v___x_224_, v___x_221_, v___x_221_, v___x_267_);
v___x_269_ = lean_unsigned_to_nat(13u);
v___x_270_ = lean_mk_empty_array_with_capacity(v___x_269_);
v___x_271_ = lean_array_push(v___x_270_, v___x_230_);
lean_inc_ref_n(v___x_232_, 5);
v___x_272_ = lean_array_push(v___x_271_, v___x_232_);
v___x_273_ = lean_array_push(v___x_272_, v___x_238_);
v___x_274_ = lean_array_push(v___x_273_, v___x_232_);
v___x_275_ = lean_array_push(v___x_274_, v___x_244_);
v___x_276_ = lean_array_push(v___x_275_, v___x_232_);
v___x_277_ = lean_array_push(v___x_276_, v___x_250_);
v___x_278_ = lean_array_push(v___x_277_, v___x_232_);
v___x_279_ = lean_array_push(v___x_278_, v___x_256_);
v___x_280_ = lean_array_push(v___x_279_, v___x_232_);
v___x_281_ = lean_array_push(v___x_280_, v___x_262_);
v___x_282_ = lean_array_push(v___x_281_, v___x_232_);
v___x_283_ = lean_array_push(v___x_282_, v___x_268_);
v___x_284_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_284_, 0, v___x_190_);
lean_ctor_set(v___x_284_, 1, v___x_196_);
lean_ctor_set(v___x_284_, 2, v___x_283_);
v___x_285_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__77));
v___x_286_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_286_, 0, v___x_190_);
lean_ctor_set(v___x_286_, 1, v___x_285_);
v___x_287_ = l_Lean_Syntax_node3(v___x_190_, v___x_196_, v___x_223_, v___x_284_, v___x_286_);
v___x_288_ = l_Lean_Syntax_node6(v___x_190_, v___x_198_, v___x_199_, v___x_219_, v___x_221_, v___x_221_, v___x_287_, v___x_221_);
v___x_289_ = l_Lean_Syntax_node1(v___x_190_, v___x_196_, v___x_288_);
v___x_290_ = l_Lean_Syntax_node1(v___x_190_, v___x_195_, v___x_289_);
v___x_291_ = l_Lean_Syntax_node1(v___x_190_, v___x_194_, v___x_290_);
v___x_292_ = l_Lean_Syntax_node2(v___x_190_, v___x_191_, v___x_193_, v___x_291_);
v___x_293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_293_, 0, v___x_292_);
lean_ctor_set(v___x_293_, 1, v_a_181_);
return v___x_293_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___boxed(lean_object* v_x_294_, lean_object* v_a_295_, lean_object* v_a_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1(v_x_294_, v_a_295_, v_a_296_);
lean_dec_ref(v_a_295_);
return v_res_297_;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__4(void){
_start:
{
lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_318_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__3));
v___x_319_ = l_String_toRawSubstring_x27(v___x_318_);
return v___x_319_;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__8(void){
_start:
{
lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_324_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__7));
v___x_325_ = l_String_toRawSubstring_x27(v___x_324_);
return v___x_325_;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__13(void){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_335_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__12));
v___x_336_ = l_String_toRawSubstring_x27(v___x_335_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticClean__wf__1(lean_object* v_x_339_, lean_object* v_a_340_, lean_object* v_a_341_){
_start:
{
lean_object* v___x_342_; uint8_t v___x_343_; 
v___x_342_ = ((lean_object*)(l_tacticClean__wf___closed__1));
v___x_343_ = l_Lean_Syntax_isOfKind(v_x_339_, v___x_342_);
if (v___x_343_ == 0)
{
lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_344_ = lean_box(1);
v___x_345_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_345_, 0, v___x_344_);
lean_ctor_set(v___x_345_, 1, v_a_341_);
return v___x_345_;
}
else
{
lean_object* v_quotContext_346_; lean_object* v_currMacroScope_347_; lean_object* v_ref_348_; uint8_t v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v_quotContext_346_ = lean_ctor_get(v_a_340_, 1);
v_currMacroScope_347_ = lean_ctor_get(v_a_340_, 2);
v_ref_348_ = lean_ctor_get(v_a_340_, 5);
v___x_349_ = 0;
v___x_350_ = l_Lean_SourceInfo_fromRef(v_ref_348_, v___x_349_);
v___x_351_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__12));
v___x_352_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__13));
lean_inc_n(v___x_350_, 40);
v___x_353_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_353_, 0, v___x_350_);
lean_ctor_set(v___x_353_, 1, v___x_351_);
v___x_354_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__15));
v___x_355_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__11));
v___x_356_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__17));
v___x_357_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__19));
v___x_358_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__20));
v___x_359_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_359_, 0, v___x_350_);
lean_ctor_set(v___x_359_, 1, v___x_358_);
v___x_360_ = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__22, &l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__22_once, _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__22);
v___x_361_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__23));
lean_inc_n(v_currMacroScope_347_, 12);
lean_inc_n(v_quotContext_346_, 12);
v___x_362_ = l_Lean_addMacroScope(v_quotContext_346_, v___x_361_, v_currMacroScope_347_);
v___x_363_ = lean_box(0);
v___x_364_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_364_, 0, v___x_350_);
lean_ctor_set(v___x_364_, 1, v___x_360_);
lean_ctor_set(v___x_364_, 2, v___x_362_);
lean_ctor_set(v___x_364_, 3, v___x_363_);
lean_inc_ref(v___x_359_);
v___x_365_ = l_Lean_Syntax_node2(v___x_350_, v___x_357_, v___x_359_, v___x_364_);
v___x_366_ = l_Lean_Syntax_node1(v___x_350_, v___x_356_, v___x_365_);
v___x_367_ = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__25, &l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__25_once, _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__25);
v___x_368_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__26));
v___x_369_ = l_Lean_addMacroScope(v_quotContext_346_, v___x_368_, v_currMacroScope_347_);
v___x_370_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_370_, 0, v___x_350_);
lean_ctor_set(v___x_370_, 1, v___x_367_);
lean_ctor_set(v___x_370_, 2, v___x_369_);
lean_ctor_set(v___x_370_, 3, v___x_363_);
v___x_371_ = l_Lean_Syntax_node2(v___x_350_, v___x_357_, v___x_359_, v___x_370_);
v___x_372_ = l_Lean_Syntax_node1(v___x_350_, v___x_356_, v___x_371_);
v___x_373_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__1));
v___x_374_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__2));
v___x_375_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_375_, 0, v___x_350_);
lean_ctor_set(v___x_375_, 1, v___x_374_);
v___x_376_ = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__4, &l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__4_once, _init_l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__4);
v___x_377_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__5));
v___x_378_ = l_Lean_addMacroScope(v_quotContext_346_, v___x_377_, v_currMacroScope_347_);
v___x_379_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_379_, 0, v___x_350_);
lean_ctor_set(v___x_379_, 1, v___x_376_);
lean_ctor_set(v___x_379_, 2, v___x_378_);
lean_ctor_set(v___x_379_, 3, v___x_363_);
v___x_380_ = l_Lean_Syntax_node2(v___x_350_, v___x_373_, v___x_375_, v___x_379_);
v___x_381_ = l_Lean_Syntax_node1(v___x_350_, v___x_356_, v___x_380_);
v___x_382_ = l_Lean_Syntax_node3(v___x_350_, v___x_355_, v___x_366_, v___x_372_, v___x_381_);
v___x_383_ = l_Lean_Syntax_node1(v___x_350_, v___x_354_, v___x_382_);
v___x_384_ = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__27, &l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__27_once, _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__27);
v___x_385_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_385_, 0, v___x_350_);
lean_ctor_set(v___x_385_, 1, v___x_355_);
lean_ctor_set(v___x_385_, 2, v___x_384_);
v___x_386_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__6));
v___x_387_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_387_, 0, v___x_350_);
lean_ctor_set(v___x_387_, 1, v___x_386_);
v___x_388_ = l_Lean_Syntax_node1(v___x_350_, v___x_355_, v___x_387_);
v___x_389_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__28));
v___x_390_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_390_, 0, v___x_350_);
lean_ctor_set(v___x_390_, 1, v___x_389_);
v___x_391_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__30));
v___x_392_ = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__32, &l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__32_once, _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__32);
v___x_393_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__33));
v___x_394_ = l_Lean_addMacroScope(v_quotContext_346_, v___x_393_, v_currMacroScope_347_);
v___x_395_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__35));
v___x_396_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_396_, 0, v___x_350_);
lean_ctor_set(v___x_396_, 1, v___x_392_);
lean_ctor_set(v___x_396_, 2, v___x_394_);
lean_ctor_set(v___x_396_, 3, v___x_395_);
lean_inc_ref_n(v___x_385_, 19);
v___x_397_ = l_Lean_Syntax_node3(v___x_350_, v___x_391_, v___x_385_, v___x_385_, v___x_396_);
v___x_398_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__36));
v___x_399_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_399_, 0, v___x_350_);
lean_ctor_set(v___x_399_, 1, v___x_398_);
v___x_400_ = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__38, &l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__38_once, _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__38);
v___x_401_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__39));
v___x_402_ = l_Lean_addMacroScope(v_quotContext_346_, v___x_401_, v_currMacroScope_347_);
v___x_403_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__43));
v___x_404_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_404_, 0, v___x_350_);
lean_ctor_set(v___x_404_, 1, v___x_400_);
lean_ctor_set(v___x_404_, 2, v___x_402_);
lean_ctor_set(v___x_404_, 3, v___x_403_);
v___x_405_ = l_Lean_Syntax_node3(v___x_350_, v___x_391_, v___x_385_, v___x_385_, v___x_404_);
v___x_406_ = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__45, &l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__45_once, _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__45);
v___x_407_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__48));
v___x_408_ = l_Lean_addMacroScope(v_quotContext_346_, v___x_407_, v_currMacroScope_347_);
v___x_409_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__52));
v___x_410_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_410_, 0, v___x_350_);
lean_ctor_set(v___x_410_, 1, v___x_406_);
lean_ctor_set(v___x_410_, 2, v___x_408_);
lean_ctor_set(v___x_410_, 3, v___x_409_);
v___x_411_ = l_Lean_Syntax_node3(v___x_350_, v___x_391_, v___x_385_, v___x_385_, v___x_410_);
v___x_412_ = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__54, &l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__54_once, _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__54);
v___x_413_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__55));
v___x_414_ = l_Lean_addMacroScope(v_quotContext_346_, v___x_413_, v_currMacroScope_347_);
v___x_415_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__57));
v___x_416_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_416_, 0, v___x_350_);
lean_ctor_set(v___x_416_, 1, v___x_412_);
lean_ctor_set(v___x_416_, 2, v___x_414_);
lean_ctor_set(v___x_416_, 3, v___x_415_);
v___x_417_ = l_Lean_Syntax_node3(v___x_350_, v___x_391_, v___x_385_, v___x_385_, v___x_416_);
v___x_418_ = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__59, &l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__59_once, _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__59);
v___x_419_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__60));
v___x_420_ = l_Lean_addMacroScope(v_quotContext_346_, v___x_419_, v_currMacroScope_347_);
v___x_421_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__62));
v___x_422_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_422_, 0, v___x_350_);
lean_ctor_set(v___x_422_, 1, v___x_418_);
lean_ctor_set(v___x_422_, 2, v___x_420_);
lean_ctor_set(v___x_422_, 3, v___x_421_);
v___x_423_ = l_Lean_Syntax_node3(v___x_350_, v___x_391_, v___x_385_, v___x_385_, v___x_422_);
v___x_424_ = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__64, &l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__64_once, _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__64);
v___x_425_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__67));
v___x_426_ = l_Lean_addMacroScope(v_quotContext_346_, v___x_425_, v_currMacroScope_347_);
v___x_427_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__69));
v___x_428_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_428_, 0, v___x_350_);
lean_ctor_set(v___x_428_, 1, v___x_424_);
lean_ctor_set(v___x_428_, 2, v___x_426_);
lean_ctor_set(v___x_428_, 3, v___x_427_);
v___x_429_ = l_Lean_Syntax_node3(v___x_350_, v___x_391_, v___x_385_, v___x_385_, v___x_428_);
v___x_430_ = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__71, &l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__71_once, _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__71);
v___x_431_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__74));
v___x_432_ = l_Lean_addMacroScope(v_quotContext_346_, v___x_431_, v_currMacroScope_347_);
v___x_433_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__76));
v___x_434_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_434_, 0, v___x_350_);
lean_ctor_set(v___x_434_, 1, v___x_430_);
lean_ctor_set(v___x_434_, 2, v___x_432_);
lean_ctor_set(v___x_434_, 3, v___x_433_);
v___x_435_ = l_Lean_Syntax_node3(v___x_350_, v___x_391_, v___x_385_, v___x_385_, v___x_434_);
v___x_436_ = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__8, &l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__8_once, _init_l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__8);
v___x_437_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__9));
v___x_438_ = l_Lean_addMacroScope(v_quotContext_346_, v___x_437_, v_currMacroScope_347_);
v___x_439_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__11));
v___x_440_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_440_, 0, v___x_350_);
lean_ctor_set(v___x_440_, 1, v___x_436_);
lean_ctor_set(v___x_440_, 2, v___x_438_);
lean_ctor_set(v___x_440_, 3, v___x_439_);
v___x_441_ = l_Lean_Syntax_node3(v___x_350_, v___x_391_, v___x_385_, v___x_385_, v___x_440_);
v___x_442_ = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__13, &l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__13_once, _init_l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__13);
v___x_443_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__14));
v___x_444_ = l_Lean_addMacroScope(v_quotContext_346_, v___x_443_, v_currMacroScope_347_);
v___x_445_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_445_, 0, v___x_350_);
lean_ctor_set(v___x_445_, 1, v___x_442_);
lean_ctor_set(v___x_445_, 2, v___x_444_);
lean_ctor_set(v___x_445_, 3, v___x_363_);
v___x_446_ = l_Lean_Syntax_node3(v___x_350_, v___x_391_, v___x_385_, v___x_385_, v___x_445_);
v___x_447_ = lean_unsigned_to_nat(17u);
v___x_448_ = lean_mk_empty_array_with_capacity(v___x_447_);
v___x_449_ = lean_array_push(v___x_448_, v___x_397_);
lean_inc_ref_n(v___x_399_, 7);
v___x_450_ = lean_array_push(v___x_449_, v___x_399_);
v___x_451_ = lean_array_push(v___x_450_, v___x_405_);
v___x_452_ = lean_array_push(v___x_451_, v___x_399_);
v___x_453_ = lean_array_push(v___x_452_, v___x_411_);
v___x_454_ = lean_array_push(v___x_453_, v___x_399_);
v___x_455_ = lean_array_push(v___x_454_, v___x_417_);
v___x_456_ = lean_array_push(v___x_455_, v___x_399_);
v___x_457_ = lean_array_push(v___x_456_, v___x_423_);
v___x_458_ = lean_array_push(v___x_457_, v___x_399_);
v___x_459_ = lean_array_push(v___x_458_, v___x_429_);
v___x_460_ = lean_array_push(v___x_459_, v___x_399_);
v___x_461_ = lean_array_push(v___x_460_, v___x_435_);
v___x_462_ = lean_array_push(v___x_461_, v___x_399_);
v___x_463_ = lean_array_push(v___x_462_, v___x_441_);
v___x_464_ = lean_array_push(v___x_463_, v___x_399_);
v___x_465_ = lean_array_push(v___x_464_, v___x_446_);
v___x_466_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_466_, 0, v___x_350_);
lean_ctor_set(v___x_466_, 1, v___x_355_);
lean_ctor_set(v___x_466_, 2, v___x_465_);
v___x_467_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__77));
v___x_468_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_468_, 0, v___x_350_);
lean_ctor_set(v___x_468_, 1, v___x_467_);
v___x_469_ = l_Lean_Syntax_node3(v___x_350_, v___x_355_, v___x_390_, v___x_466_, v___x_468_);
v___x_470_ = l_Lean_Syntax_node6(v___x_350_, v___x_352_, v___x_353_, v___x_383_, v___x_385_, v___x_388_, v___x_469_, v___x_385_);
v___x_471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_471_, 0, v___x_470_);
lean_ctor_set(v___x_471_, 1, v_a_341_);
return v___x_471_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___boxed(lean_object* v_x_472_, lean_object* v_a_473_, lean_object* v_a_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l___aux__Init__WFTactics______macroRules__tacticClean__wf__1(v_x_472_, v_a_473_, v_a_474_);
lean_dec_ref(v_a_473_);
return v_res_475_;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__6(void){
_start:
{
lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_502_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__5));
v___x_503_ = l_String_toRawSubstring_x27(v___x_502_);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1(lean_object* v_x_514_, lean_object* v_a_515_, lean_object* v_a_516_){
_start:
{
lean_object* v___x_517_; uint8_t v___x_518_; 
v___x_517_ = ((lean_object*)(l_tacticDecreasing__trivial___closed__1));
v___x_518_ = l_Lean_Syntax_isOfKind(v_x_514_, v___x_517_);
if (v___x_518_ == 0)
{
lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_519_ = lean_box(1);
v___x_520_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_520_, 0, v___x_519_);
lean_ctor_set(v___x_520_, 1, v_a_516_);
return v___x_520_;
}
else
{
lean_object* v_quotContext_521_; lean_object* v_currMacroScope_522_; lean_object* v_ref_523_; uint8_t v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v_quotContext_521_ = lean_ctor_get(v_a_515_, 1);
v_currMacroScope_522_ = lean_ctor_get(v_a_515_, 2);
v_ref_523_ = lean_ctor_get(v_a_515_, 5);
v___x_524_ = 0;
v___x_525_ = l_Lean_SourceInfo_fromRef(v_ref_523_, v___x_524_);
v___x_526_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__1));
v___x_527_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__3));
v___x_528_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__4));
lean_inc_n(v___x_525_, 22);
v___x_529_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_529_, 0, v___x_525_);
lean_ctor_set(v___x_529_, 1, v___x_528_);
v___x_530_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__7));
v___x_531_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__9));
v___x_532_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__11));
v___x_533_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__12));
v___x_534_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__13));
v___x_535_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_535_, 0, v___x_525_);
lean_ctor_set(v___x_535_, 1, v___x_533_);
v___x_536_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__15));
v___x_537_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__17));
v___x_538_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__19));
v___x_539_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__20));
v___x_540_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_540_, 0, v___x_525_);
lean_ctor_set(v___x_540_, 1, v___x_539_);
v___x_541_ = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__6, &l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__6_once, _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__6);
v___x_542_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__7));
lean_inc_n(v_currMacroScope_522_, 2);
lean_inc_n(v_quotContext_521_, 2);
v___x_543_ = l_Lean_addMacroScope(v_quotContext_521_, v___x_542_, v_currMacroScope_522_);
v___x_544_ = lean_box(0);
v___x_545_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_545_, 0, v___x_525_);
lean_ctor_set(v___x_545_, 1, v___x_541_);
lean_ctor_set(v___x_545_, 2, v___x_543_);
lean_ctor_set(v___x_545_, 3, v___x_544_);
v___x_546_ = l_Lean_Syntax_node2(v___x_525_, v___x_538_, v___x_540_, v___x_545_);
v___x_547_ = l_Lean_Syntax_node1(v___x_525_, v___x_537_, v___x_546_);
v___x_548_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__1));
v___x_549_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__2));
v___x_550_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_550_, 0, v___x_525_);
lean_ctor_set(v___x_550_, 1, v___x_549_);
v___x_551_ = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__4, &l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__4_once, _init_l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__4);
v___x_552_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__5));
v___x_553_ = l_Lean_addMacroScope(v_quotContext_521_, v___x_552_, v_currMacroScope_522_);
v___x_554_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_554_, 0, v___x_525_);
lean_ctor_set(v___x_554_, 1, v___x_551_);
lean_ctor_set(v___x_554_, 2, v___x_553_);
lean_ctor_set(v___x_554_, 3, v___x_544_);
v___x_555_ = l_Lean_Syntax_node2(v___x_525_, v___x_548_, v___x_550_, v___x_554_);
v___x_556_ = l_Lean_Syntax_node1(v___x_525_, v___x_537_, v___x_555_);
v___x_557_ = l_Lean_Syntax_node2(v___x_525_, v___x_532_, v___x_547_, v___x_556_);
v___x_558_ = l_Lean_Syntax_node1(v___x_525_, v___x_536_, v___x_557_);
v___x_559_ = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__27, &l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__27_once, _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__27);
v___x_560_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_560_, 0, v___x_525_);
lean_ctor_set(v___x_560_, 1, v___x_532_);
lean_ctor_set(v___x_560_, 2, v___x_559_);
lean_inc_ref_n(v___x_560_, 3);
v___x_561_ = l_Lean_Syntax_node6(v___x_525_, v___x_534_, v___x_535_, v___x_558_, v___x_560_, v___x_560_, v___x_560_, v___x_560_);
v___x_562_ = l_Lean_Syntax_node1(v___x_525_, v___x_532_, v___x_561_);
v___x_563_ = l_Lean_Syntax_node1(v___x_525_, v___x_531_, v___x_562_);
v___x_564_ = l_Lean_Syntax_node1(v___x_525_, v___x_530_, v___x_563_);
v___x_565_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__8));
v___x_566_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_566_, 0, v___x_525_);
lean_ctor_set(v___x_566_, 1, v___x_565_);
v___x_567_ = l_Lean_Syntax_node3(v___x_525_, v___x_527_, v___x_529_, v___x_564_, v___x_566_);
v___x_568_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__9));
v___x_569_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_569_, 0, v___x_525_);
lean_ctor_set(v___x_569_, 1, v___x_568_);
v___x_570_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__10));
v___x_571_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__11));
v___x_572_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_572_, 0, v___x_525_);
lean_ctor_set(v___x_572_, 1, v___x_570_);
v___x_573_ = l_Lean_Syntax_node1(v___x_525_, v___x_571_, v___x_572_);
v___x_574_ = l_Lean_Syntax_node3(v___x_525_, v___x_526_, v___x_567_, v___x_569_, v___x_573_);
v___x_575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_575_, 0, v___x_574_);
lean_ctor_set(v___x_575_, 1, v_a_516_);
return v___x_575_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___boxed(lean_object* v_x_576_, lean_object* v_a_577_, lean_object* v_a_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1(v_x_576_, v_a_577_, v_a_578_);
lean_dec_ref(v_a_577_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__2(lean_object* v_x_586_, lean_object* v_a_587_, lean_object* v_a_588_){
_start:
{
lean_object* v___x_589_; uint8_t v___x_590_; 
v___x_589_ = ((lean_object*)(l_tacticDecreasing__trivial___closed__1));
v___x_590_ = l_Lean_Syntax_isOfKind(v_x_586_, v___x_589_);
if (v___x_590_ == 0)
{
lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_591_ = lean_box(1);
v___x_592_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_592_, 0, v___x_591_);
lean_ctor_set(v___x_592_, 1, v_a_588_);
return v___x_592_;
}
else
{
lean_object* v_ref_593_; uint8_t v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; 
v_ref_593_ = lean_ctor_get(v_a_587_, 5);
v___x_594_ = 0;
v___x_595_ = l_Lean_SourceInfo_fromRef(v_ref_593_, v___x_594_);
v___x_596_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__2___closed__0));
v___x_597_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__2___closed__1));
lean_inc_n(v___x_595_, 3);
v___x_598_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_598_, 0, v___x_595_);
lean_ctor_set(v___x_598_, 1, v___x_596_);
v___x_599_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__15));
v___x_600_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__11));
v___x_601_ = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__27, &l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__27_once, _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__27);
v___x_602_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_602_, 0, v___x_595_);
lean_ctor_set(v___x_602_, 1, v___x_600_);
lean_ctor_set(v___x_602_, 2, v___x_601_);
v___x_603_ = l_Lean_Syntax_node1(v___x_595_, v___x_599_, v___x_602_);
v___x_604_ = l_Lean_Syntax_node2(v___x_595_, v___x_597_, v___x_598_, v___x_603_);
v___x_605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_605_, 0, v___x_604_);
lean_ctor_set(v___x_605_, 1, v_a_588_);
return v___x_605_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__2___boxed(lean_object* v_x_606_, lean_object* v_a_607_, lean_object* v_a_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__2(v_x_606_, v_a_607_, v_a_608_);
lean_dec_ref(v_a_607_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3(lean_object* v_x_616_, lean_object* v_a_617_, lean_object* v_a_618_){
_start:
{
lean_object* v___x_619_; uint8_t v___x_620_; 
v___x_619_ = ((lean_object*)(l_tacticDecreasing__trivial___closed__1));
v___x_620_ = l_Lean_Syntax_isOfKind(v_x_616_, v___x_619_);
if (v___x_620_ == 0)
{
lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_621_ = lean_box(1);
v___x_622_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_622_, 0, v___x_621_);
lean_ctor_set(v___x_622_, 1, v_a_618_);
return v___x_622_;
}
else
{
lean_object* v_ref_623_; uint8_t v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
v_ref_623_ = lean_ctor_get(v_a_617_, 5);
v___x_624_ = 0;
v___x_625_ = l_Lean_SourceInfo_fromRef(v_ref_623_, v___x_624_);
v___x_626_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___closed__0));
v___x_627_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___closed__1));
lean_inc(v___x_625_);
v___x_628_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_628_, 0, v___x_625_);
lean_ctor_set(v___x_628_, 1, v___x_626_);
v___x_629_ = l_Lean_Syntax_node1(v___x_625_, v___x_627_, v___x_628_);
v___x_630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_630_, 0, v___x_629_);
lean_ctor_set(v___x_630_, 1, v_a_618_);
return v___x_630_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___boxed(lean_object* v_x_631_, lean_object* v_a_632_, lean_object* v_a_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3(v_x_631_, v_a_632_, v_a_633_);
lean_dec_ref(v_a_632_);
return v_res_634_;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__5(void){
_start:
{
lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_660_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__4));
v___x_661_ = l_String_toRawSubstring_x27(v___x_660_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1(lean_object* v_x_673_, lean_object* v_a_674_, lean_object* v_a_675_){
_start:
{
lean_object* v___x_676_; uint8_t v___x_677_; 
v___x_676_ = ((lean_object*)(l_tacticDecreasing__trivial__pre__omega___closed__1));
v___x_677_ = l_Lean_Syntax_isOfKind(v_x_673_, v___x_676_);
if (v___x_677_ == 0)
{
lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_678_ = lean_box(1);
v___x_679_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_679_, 0, v___x_678_);
lean_ctor_set(v___x_679_, 1, v_a_675_);
return v___x_679_;
}
else
{
lean_object* v_quotContext_680_; lean_object* v_currMacroScope_681_; lean_object* v_ref_682_; uint8_t v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; 
v_quotContext_680_ = lean_ctor_get(v_a_674_, 1);
v_currMacroScope_681_ = lean_ctor_get(v_a_674_, 2);
v_ref_682_ = lean_ctor_get(v_a_674_, 5);
v___x_683_ = 0;
v___x_684_ = l_Lean_SourceInfo_fromRef(v_ref_682_, v___x_683_);
v___x_685_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__1));
v___x_686_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__11));
v___x_687_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__2));
v___x_688_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__3));
lean_inc_n(v___x_684_, 7);
v___x_689_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_689_, 0, v___x_684_);
lean_ctor_set(v___x_689_, 1, v___x_687_);
v___x_690_ = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__5, &l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__5_once, _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__5);
v___x_691_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__7));
lean_inc(v_currMacroScope_681_);
lean_inc(v_quotContext_680_);
v___x_692_ = l_Lean_addMacroScope(v_quotContext_680_, v___x_691_, v_currMacroScope_681_);
v___x_693_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__9));
v___x_694_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_694_, 0, v___x_684_);
lean_ctor_set(v___x_694_, 1, v___x_690_);
lean_ctor_set(v___x_694_, 2, v___x_692_);
lean_ctor_set(v___x_694_, 3, v___x_693_);
v___x_695_ = l_Lean_Syntax_node2(v___x_684_, v___x_688_, v___x_689_, v___x_694_);
v___x_696_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__10));
v___x_697_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_697_, 0, v___x_684_);
lean_ctor_set(v___x_697_, 1, v___x_696_);
v___x_698_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___closed__0));
v___x_699_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___closed__1));
v___x_700_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_700_, 0, v___x_684_);
lean_ctor_set(v___x_700_, 1, v___x_698_);
v___x_701_ = l_Lean_Syntax_node1(v___x_684_, v___x_699_, v___x_700_);
v___x_702_ = l_Lean_Syntax_node3(v___x_684_, v___x_686_, v___x_695_, v___x_697_, v___x_701_);
v___x_703_ = l_Lean_Syntax_node1(v___x_684_, v___x_685_, v___x_702_);
v___x_704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_704_, 0, v___x_703_);
lean_ctor_set(v___x_704_, 1, v_a_675_);
return v___x_704_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___boxed(lean_object* v_x_705_, lean_object* v_a_706_, lean_object* v_a_707_){
_start:
{
lean_object* v_res_708_; 
v_res_708_ = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1(v_x_705_, v_a_706_, v_a_707_);
lean_dec_ref(v_a_706_);
return v_res_708_;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__1(void){
_start:
{
lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_710_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__0));
v___x_711_ = l_String_toRawSubstring_x27(v___x_710_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2(lean_object* v_x_722_, lean_object* v_a_723_, lean_object* v_a_724_){
_start:
{
lean_object* v___x_725_; uint8_t v___x_726_; 
v___x_725_ = ((lean_object*)(l_tacticDecreasing__trivial__pre__omega___closed__1));
v___x_726_ = l_Lean_Syntax_isOfKind(v_x_722_, v___x_725_);
if (v___x_726_ == 0)
{
lean_object* v___x_727_; lean_object* v___x_728_; 
v___x_727_ = lean_box(1);
v___x_728_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_728_, 0, v___x_727_);
lean_ctor_set(v___x_728_, 1, v_a_724_);
return v___x_728_;
}
else
{
lean_object* v_quotContext_729_; lean_object* v_currMacroScope_730_; lean_object* v_ref_731_; uint8_t v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
v_quotContext_729_ = lean_ctor_get(v_a_723_, 1);
v_currMacroScope_730_ = lean_ctor_get(v_a_723_, 2);
v_ref_731_ = lean_ctor_get(v_a_723_, 5);
v___x_732_ = 0;
v___x_733_ = l_Lean_SourceInfo_fromRef(v_ref_731_, v___x_732_);
v___x_734_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__1));
v___x_735_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__11));
v___x_736_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__2));
v___x_737_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__3));
lean_inc_n(v___x_733_, 7);
v___x_738_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_738_, 0, v___x_733_);
lean_ctor_set(v___x_738_, 1, v___x_736_);
v___x_739_ = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__1, &l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__1_once, _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__1);
v___x_740_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__3));
lean_inc(v_currMacroScope_730_);
lean_inc(v_quotContext_729_);
v___x_741_ = l_Lean_addMacroScope(v_quotContext_729_, v___x_740_, v_currMacroScope_730_);
v___x_742_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__5));
v___x_743_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_743_, 0, v___x_733_);
lean_ctor_set(v___x_743_, 1, v___x_739_);
lean_ctor_set(v___x_743_, 2, v___x_741_);
lean_ctor_set(v___x_743_, 3, v___x_742_);
v___x_744_ = l_Lean_Syntax_node2(v___x_733_, v___x_737_, v___x_738_, v___x_743_);
v___x_745_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__10));
v___x_746_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_746_, 0, v___x_733_);
lean_ctor_set(v___x_746_, 1, v___x_745_);
v___x_747_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___closed__0));
v___x_748_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___closed__1));
v___x_749_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_749_, 0, v___x_733_);
lean_ctor_set(v___x_749_, 1, v___x_747_);
v___x_750_ = l_Lean_Syntax_node1(v___x_733_, v___x_748_, v___x_749_);
v___x_751_ = l_Lean_Syntax_node3(v___x_733_, v___x_735_, v___x_744_, v___x_746_, v___x_750_);
v___x_752_ = l_Lean_Syntax_node1(v___x_733_, v___x_734_, v___x_751_);
v___x_753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_753_, 0, v___x_752_);
lean_ctor_set(v___x_753_, 1, v_a_724_);
return v___x_753_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___boxed(lean_object* v_x_754_, lean_object* v_a_755_, lean_object* v_a_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2(v_x_754_, v_a_755_, v_a_756_);
lean_dec_ref(v_a_755_);
return v_res_757_;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__1(void){
_start:
{
lean_object* v___x_759_; lean_object* v___x_760_; 
v___x_759_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__0));
v___x_760_ = l_String_toRawSubstring_x27(v___x_759_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3(lean_object* v_x_771_, lean_object* v_a_772_, lean_object* v_a_773_){
_start:
{
lean_object* v___x_774_; uint8_t v___x_775_; 
v___x_774_ = ((lean_object*)(l_tacticDecreasing__trivial__pre__omega___closed__1));
v___x_775_ = l_Lean_Syntax_isOfKind(v_x_771_, v___x_774_);
if (v___x_775_ == 0)
{
lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_776_ = lean_box(1);
v___x_777_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_777_, 0, v___x_776_);
lean_ctor_set(v___x_777_, 1, v_a_773_);
return v___x_777_;
}
else
{
lean_object* v_quotContext_778_; lean_object* v_currMacroScope_779_; lean_object* v_ref_780_; uint8_t v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
v_quotContext_778_ = lean_ctor_get(v_a_772_, 1);
v_currMacroScope_779_ = lean_ctor_get(v_a_772_, 2);
v_ref_780_ = lean_ctor_get(v_a_772_, 5);
v___x_781_ = 0;
v___x_782_ = l_Lean_SourceInfo_fromRef(v_ref_780_, v___x_781_);
v___x_783_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__1));
v___x_784_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__11));
v___x_785_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__2));
v___x_786_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__3));
lean_inc_n(v___x_782_, 7);
v___x_787_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_787_, 0, v___x_782_);
lean_ctor_set(v___x_787_, 1, v___x_785_);
v___x_788_ = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__1, &l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__1_once, _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__1);
v___x_789_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__3));
lean_inc(v_currMacroScope_779_);
lean_inc(v_quotContext_778_);
v___x_790_ = l_Lean_addMacroScope(v_quotContext_778_, v___x_789_, v_currMacroScope_779_);
v___x_791_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__5));
v___x_792_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_792_, 0, v___x_782_);
lean_ctor_set(v___x_792_, 1, v___x_788_);
lean_ctor_set(v___x_792_, 2, v___x_790_);
lean_ctor_set(v___x_792_, 3, v___x_791_);
v___x_793_ = l_Lean_Syntax_node2(v___x_782_, v___x_786_, v___x_787_, v___x_792_);
v___x_794_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__10));
v___x_795_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_795_, 0, v___x_782_);
lean_ctor_set(v___x_795_, 1, v___x_794_);
v___x_796_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___closed__0));
v___x_797_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___closed__1));
v___x_798_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_798_, 0, v___x_782_);
lean_ctor_set(v___x_798_, 1, v___x_796_);
v___x_799_ = l_Lean_Syntax_node1(v___x_782_, v___x_797_, v___x_798_);
v___x_800_ = l_Lean_Syntax_node3(v___x_782_, v___x_784_, v___x_793_, v___x_795_, v___x_799_);
v___x_801_ = l_Lean_Syntax_node1(v___x_782_, v___x_783_, v___x_800_);
v___x_802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_802_, 0, v___x_801_);
lean_ctor_set(v___x_802_, 1, v_a_773_);
return v___x_802_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___boxed(lean_object* v_x_803_, lean_object* v_a_804_, lean_object* v_a_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3(v_x_803_, v_a_804_, v_a_805_);
lean_dec_ref(v_a_804_);
return v_res_806_;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__9(void){
_start:
{
lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_848_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__8));
v___x_849_ = l_String_toRawSubstring_x27(v___x_848_);
return v___x_849_;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__16(void){
_start:
{
lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_863_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__15));
v___x_864_ = l_String_toRawSubstring_x27(v___x_863_);
return v___x_864_;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__22(void){
_start:
{
lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_877_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__21));
v___x_878_ = l_String_toRawSubstring_x27(v___x_877_);
return v___x_878_;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__28(void){
_start:
{
lean_object* v___x_891_; lean_object* v___x_892_; 
v___x_891_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__27));
v___x_892_ = l_String_toRawSubstring_x27(v___x_891_);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1(lean_object* v_x_913_, lean_object* v_a_914_, lean_object* v_a_915_){
_start:
{
lean_object* v___x_916_; uint8_t v___x_917_; 
v___x_916_ = ((lean_object*)(l_tacticDecreasing__with___00__closed__1));
lean_inc(v_x_913_);
v___x_917_ = l_Lean_Syntax_isOfKind(v_x_913_, v___x_916_);
if (v___x_917_ == 0)
{
lean_object* v___x_918_; lean_object* v___x_919_; 
lean_dec(v_x_913_);
v___x_918_ = lean_box(1);
v___x_919_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_919_, 0, v___x_918_);
lean_ctor_set(v___x_919_, 1, v_a_915_);
return v___x_919_;
}
else
{
lean_object* v_quotContext_920_; lean_object* v_currMacroScope_921_; lean_object* v_ref_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; uint8_t v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; 
v_quotContext_920_ = lean_ctor_get(v_a_914_, 1);
v_currMacroScope_921_ = lean_ctor_get(v_a_914_, 2);
v_ref_922_ = lean_ctor_get(v_a_914_, 5);
v___x_923_ = lean_unsigned_to_nat(1u);
v___x_924_ = l_Lean_Syntax_getArg(v_x_913_, v___x_923_);
lean_dec(v_x_913_);
v___x_925_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__7));
v___x_926_ = 0;
v___x_927_ = l_Lean_SourceInfo_fromRef(v_ref_922_, v___x_926_);
v___x_928_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__3));
v___x_929_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__4));
lean_inc_n(v___x_927_, 82);
v___x_930_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_930_, 0, v___x_927_);
lean_ctor_set(v___x_930_, 1, v___x_929_);
v___x_931_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__9));
v___x_932_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__11));
v___x_933_ = ((lean_object*)(l_tacticClean__wf___closed__1));
v___x_934_ = ((lean_object*)(l_tacticClean__wf___closed__2));
v___x_935_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_935_, 0, v___x_927_);
lean_ctor_set(v___x_935_, 1, v___x_934_);
v___x_936_ = l_Lean_Syntax_node1(v___x_927_, v___x_933_, v___x_935_);
v___x_937_ = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__27, &l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__27_once, _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__27);
v___x_938_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_938_, 0, v___x_927_);
lean_ctor_set(v___x_938_, 1, v___x_932_);
lean_ctor_set(v___x_938_, 2, v___x_937_);
v___x_939_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__4));
v___x_940_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__5));
v___x_941_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_941_, 0, v___x_927_);
lean_ctor_set(v___x_941_, 1, v___x_940_);
v___x_942_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__12));
v___x_943_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__13));
v___x_944_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_944_, 0, v___x_927_);
lean_ctor_set(v___x_944_, 1, v___x_942_);
v___x_945_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__15));
lean_inc_ref_n(v___x_938_, 8);
v___x_946_ = l_Lean_Syntax_node1(v___x_927_, v___x_945_, v___x_938_);
v___x_947_ = l_Lean_Syntax_node6(v___x_927_, v___x_943_, v___x_944_, v___x_946_, v___x_938_, v___x_938_, v___x_938_, v___x_938_);
v___x_948_ = l_Lean_Syntax_node1(v___x_927_, v___x_932_, v___x_947_);
v___x_949_ = l_Lean_Syntax_node1(v___x_927_, v___x_931_, v___x_948_);
v___x_950_ = l_Lean_Syntax_node1(v___x_927_, v___x_925_, v___x_949_);
v___x_951_ = l_Lean_Syntax_node2(v___x_927_, v___x_939_, v___x_941_, v___x_950_);
v___x_952_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__1));
v___x_953_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__2));
v___x_954_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_954_, 0, v___x_927_);
lean_ctor_set(v___x_954_, 1, v___x_953_);
v___x_955_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__3));
v___x_956_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__4));
v___x_957_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_957_, 0, v___x_927_);
lean_ctor_set(v___x_957_, 1, v___x_955_);
v___x_958_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__6));
v___x_959_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__7));
v___x_960_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_960_, 0, v___x_927_);
lean_ctor_set(v___x_960_, 1, v___x_959_);
v___x_961_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__2));
v___x_962_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__3));
v___x_963_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_963_, 0, v___x_927_);
lean_ctor_set(v___x_963_, 1, v___x_961_);
v___x_964_ = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__9, &l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__9_once, _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__9);
v___x_965_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__12));
lean_inc_n(v_currMacroScope_921_, 4);
lean_inc_n(v_quotContext_920_, 4);
v___x_966_ = l_Lean_addMacroScope(v_quotContext_920_, v___x_965_, v_currMacroScope_921_);
v___x_967_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__14));
v___x_968_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_968_, 0, v___x_927_);
lean_ctor_set(v___x_968_, 1, v___x_964_);
lean_ctor_set(v___x_968_, 2, v___x_966_);
lean_ctor_set(v___x_968_, 3, v___x_967_);
lean_inc_ref_n(v___x_963_, 3);
v___x_969_ = l_Lean_Syntax_node2(v___x_927_, v___x_962_, v___x_963_, v___x_968_);
v___x_970_ = l_Lean_Syntax_node1(v___x_927_, v___x_932_, v___x_969_);
v___x_971_ = l_Lean_Syntax_node1(v___x_927_, v___x_931_, v___x_970_);
v___x_972_ = l_Lean_Syntax_node1(v___x_927_, v___x_925_, v___x_971_);
lean_inc_ref_n(v___x_960_, 6);
v___x_973_ = l_Lean_Syntax_node2(v___x_927_, v___x_958_, v___x_960_, v___x_972_);
v___x_974_ = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__16, &l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__16_once, _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__16);
v___x_975_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__18));
v___x_976_ = l_Lean_addMacroScope(v_quotContext_920_, v___x_975_, v_currMacroScope_921_);
v___x_977_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__20));
v___x_978_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_978_, 0, v___x_927_);
lean_ctor_set(v___x_978_, 1, v___x_974_);
lean_ctor_set(v___x_978_, 2, v___x_976_);
lean_ctor_set(v___x_978_, 3, v___x_977_);
v___x_979_ = l_Lean_Syntax_node2(v___x_927_, v___x_962_, v___x_963_, v___x_978_);
v___x_980_ = l_Lean_Syntax_node1(v___x_927_, v___x_932_, v___x_979_);
v___x_981_ = l_Lean_Syntax_node1(v___x_927_, v___x_931_, v___x_980_);
v___x_982_ = l_Lean_Syntax_node1(v___x_927_, v___x_925_, v___x_981_);
v___x_983_ = l_Lean_Syntax_node2(v___x_927_, v___x_958_, v___x_960_, v___x_982_);
v___x_984_ = l_Lean_Syntax_node2(v___x_927_, v___x_932_, v___x_973_, v___x_983_);
lean_inc_ref_n(v___x_957_, 2);
v___x_985_ = l_Lean_Syntax_node2(v___x_927_, v___x_956_, v___x_957_, v___x_984_);
v___x_986_ = l_Lean_Syntax_node1(v___x_927_, v___x_932_, v___x_985_);
v___x_987_ = l_Lean_Syntax_node1(v___x_927_, v___x_931_, v___x_986_);
v___x_988_ = l_Lean_Syntax_node1(v___x_927_, v___x_925_, v___x_987_);
v___x_989_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__8));
v___x_990_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_990_, 0, v___x_927_);
lean_ctor_set(v___x_990_, 1, v___x_989_);
lean_inc_ref_n(v___x_990_, 2);
lean_inc_ref_n(v___x_930_, 2);
v___x_991_ = l_Lean_Syntax_node3(v___x_927_, v___x_928_, v___x_930_, v___x_988_, v___x_990_);
v___x_992_ = l_Lean_Syntax_node1(v___x_927_, v___x_932_, v___x_991_);
v___x_993_ = l_Lean_Syntax_node1(v___x_927_, v___x_931_, v___x_992_);
v___x_994_ = l_Lean_Syntax_node1(v___x_927_, v___x_925_, v___x_993_);
lean_inc_ref(v___x_954_);
v___x_995_ = l_Lean_Syntax_node2(v___x_927_, v___x_952_, v___x_954_, v___x_994_);
v___x_996_ = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__22, &l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__22_once, _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__22);
v___x_997_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__24));
v___x_998_ = l_Lean_addMacroScope(v_quotContext_920_, v___x_997_, v_currMacroScope_921_);
v___x_999_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__26));
v___x_1000_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1000_, 0, v___x_927_);
lean_ctor_set(v___x_1000_, 1, v___x_996_);
lean_ctor_set(v___x_1000_, 2, v___x_998_);
lean_ctor_set(v___x_1000_, 3, v___x_999_);
v___x_1001_ = l_Lean_Syntax_node2(v___x_927_, v___x_962_, v___x_963_, v___x_1000_);
v___x_1002_ = l_Lean_Syntax_node1(v___x_927_, v___x_932_, v___x_1001_);
v___x_1003_ = l_Lean_Syntax_node1(v___x_927_, v___x_931_, v___x_1002_);
v___x_1004_ = l_Lean_Syntax_node1(v___x_927_, v___x_925_, v___x_1003_);
v___x_1005_ = l_Lean_Syntax_node2(v___x_927_, v___x_958_, v___x_960_, v___x_1004_);
v___x_1006_ = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__28, &l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__28_once, _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__28);
v___x_1007_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__29));
v___x_1008_ = l_Lean_addMacroScope(v_quotContext_920_, v___x_1007_, v_currMacroScope_921_);
v___x_1009_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__31));
v___x_1010_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1010_, 0, v___x_927_);
lean_ctor_set(v___x_1010_, 1, v___x_1006_);
lean_ctor_set(v___x_1010_, 2, v___x_1008_);
lean_ctor_set(v___x_1010_, 3, v___x_1009_);
v___x_1011_ = l_Lean_Syntax_node2(v___x_927_, v___x_962_, v___x_963_, v___x_1010_);
v___x_1012_ = l_Lean_Syntax_node1(v___x_927_, v___x_932_, v___x_1011_);
v___x_1013_ = l_Lean_Syntax_node1(v___x_927_, v___x_931_, v___x_1012_);
v___x_1014_ = l_Lean_Syntax_node1(v___x_927_, v___x_925_, v___x_1013_);
v___x_1015_ = l_Lean_Syntax_node2(v___x_927_, v___x_958_, v___x_960_, v___x_1014_);
v___x_1016_ = l_Lean_Syntax_node2(v___x_927_, v___x_932_, v___x_1005_, v___x_1015_);
v___x_1017_ = l_Lean_Syntax_node2(v___x_927_, v___x_956_, v___x_957_, v___x_1016_);
v___x_1018_ = l_Lean_Syntax_node1(v___x_927_, v___x_932_, v___x_1017_);
v___x_1019_ = l_Lean_Syntax_node1(v___x_927_, v___x_931_, v___x_1018_);
v___x_1020_ = l_Lean_Syntax_node1(v___x_927_, v___x_925_, v___x_1019_);
v___x_1021_ = l_Lean_Syntax_node3(v___x_927_, v___x_928_, v___x_930_, v___x_1020_, v___x_990_);
v___x_1022_ = l_Lean_Syntax_node1(v___x_927_, v___x_932_, v___x_1021_);
v___x_1023_ = l_Lean_Syntax_node1(v___x_927_, v___x_931_, v___x_1022_);
v___x_1024_ = l_Lean_Syntax_node1(v___x_927_, v___x_925_, v___x_1023_);
v___x_1025_ = l_Lean_Syntax_node2(v___x_927_, v___x_952_, v___x_954_, v___x_1024_);
v___x_1026_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__10));
v___x_1027_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__11));
v___x_1028_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1028_, 0, v___x_927_);
lean_ctor_set(v___x_1028_, 1, v___x_1026_);
v___x_1029_ = l_Lean_Syntax_node1(v___x_927_, v___x_1027_, v___x_1028_);
v___x_1030_ = l_Lean_Syntax_node1(v___x_927_, v___x_932_, v___x_1029_);
v___x_1031_ = l_Lean_Syntax_node1(v___x_927_, v___x_931_, v___x_1030_);
v___x_1032_ = l_Lean_Syntax_node1(v___x_927_, v___x_925_, v___x_1031_);
v___x_1033_ = l_Lean_Syntax_node2(v___x_927_, v___x_958_, v___x_960_, v___x_1032_);
v___x_1034_ = l_Lean_Syntax_node2(v___x_927_, v___x_958_, v___x_960_, v___x_924_);
v___x_1035_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__32));
v___x_1036_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__33));
v___x_1037_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1037_, 0, v___x_927_);
lean_ctor_set(v___x_1037_, 1, v___x_1035_);
v___x_1038_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__35));
v___x_1039_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__36));
v___x_1040_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1040_, 0, v___x_927_);
lean_ctor_set(v___x_1040_, 1, v___x_1039_);
v___x_1041_ = l_Lean_Syntax_node1(v___x_927_, v___x_1038_, v___x_1040_);
v___x_1042_ = l_Lean_Syntax_node1(v___x_927_, v___x_932_, v___x_1041_);
v___x_1043_ = l_Lean_Syntax_node2(v___x_927_, v___x_1036_, v___x_1037_, v___x_1042_);
v___x_1044_ = l_Lean_Syntax_node1(v___x_927_, v___x_932_, v___x_1043_);
v___x_1045_ = l_Lean_Syntax_node1(v___x_927_, v___x_931_, v___x_1044_);
v___x_1046_ = l_Lean_Syntax_node1(v___x_927_, v___x_925_, v___x_1045_);
v___x_1047_ = l_Lean_Syntax_node2(v___x_927_, v___x_958_, v___x_960_, v___x_1046_);
v___x_1048_ = l_Lean_Syntax_node3(v___x_927_, v___x_932_, v___x_1033_, v___x_1034_, v___x_1047_);
v___x_1049_ = l_Lean_Syntax_node2(v___x_927_, v___x_956_, v___x_957_, v___x_1048_);
v___x_1050_ = lean_unsigned_to_nat(9u);
v___x_1051_ = lean_mk_empty_array_with_capacity(v___x_1050_);
v___x_1052_ = lean_array_push(v___x_1051_, v___x_936_);
v___x_1053_ = lean_array_push(v___x_1052_, v___x_938_);
v___x_1054_ = lean_array_push(v___x_1053_, v___x_951_);
v___x_1055_ = lean_array_push(v___x_1054_, v___x_938_);
v___x_1056_ = lean_array_push(v___x_1055_, v___x_995_);
v___x_1057_ = lean_array_push(v___x_1056_, v___x_938_);
v___x_1058_ = lean_array_push(v___x_1057_, v___x_1025_);
v___x_1059_ = lean_array_push(v___x_1058_, v___x_938_);
v___x_1060_ = lean_array_push(v___x_1059_, v___x_1049_);
v___x_1061_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1061_, 0, v___x_927_);
lean_ctor_set(v___x_1061_, 1, v___x_932_);
lean_ctor_set(v___x_1061_, 2, v___x_1060_);
v___x_1062_ = l_Lean_Syntax_node1(v___x_927_, v___x_931_, v___x_1061_);
v___x_1063_ = l_Lean_Syntax_node1(v___x_927_, v___x_925_, v___x_1062_);
v___x_1064_ = l_Lean_Syntax_node3(v___x_927_, v___x_928_, v___x_930_, v___x_1063_, v___x_990_);
v___x_1065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1064_);
lean_ctor_set(v___x_1065_, 1, v_a_915_);
return v___x_1065_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___boxed(lean_object* v_x_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_){
_start:
{
lean_object* v_res_1069_; 
v_res_1069_ = l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1(v_x_1066_, v_a_1067_, v_a_1068_);
lean_dec_ref(v_a_1067_);
return v_res_1069_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1(lean_object* v_x_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_){
_start:
{
lean_object* v___x_1093_; uint8_t v___x_1094_; 
v___x_1093_ = ((lean_object*)(l_tacticDecreasing__tactic___closed__1));
v___x_1094_ = l_Lean_Syntax_isOfKind(v_x_1090_, v___x_1093_);
if (v___x_1094_ == 0)
{
lean_object* v___x_1095_; lean_object* v___x_1096_; 
v___x_1095_ = lean_box(1);
v___x_1096_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1096_, 0, v___x_1095_);
lean_ctor_set(v___x_1096_, 1, v_a_1092_);
return v___x_1096_;
}
else
{
lean_object* v_ref_1097_; uint8_t v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; 
v_ref_1097_ = lean_ctor_get(v_a_1091_, 5);
v___x_1098_ = 0;
v___x_1099_ = l_Lean_SourceInfo_fromRef(v_ref_1097_, v___x_1098_);
v___x_1100_ = ((lean_object*)(l_tacticDecreasing__with___00__closed__1));
v___x_1101_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___closed__0));
lean_inc_n(v___x_1099_, 21);
v___x_1102_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1099_);
lean_ctor_set(v___x_1102_, 1, v___x_1101_);
v___x_1103_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__7));
v___x_1104_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__9));
v___x_1105_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__11));
v___x_1106_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__3));
v___x_1107_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__4));
v___x_1108_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1108_, 0, v___x_1099_);
lean_ctor_set(v___x_1108_, 1, v___x_1106_);
v___x_1109_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__6));
v___x_1110_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__7));
v___x_1111_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1111_, 0, v___x_1099_);
lean_ctor_set(v___x_1111_, 1, v___x_1110_);
v___x_1112_ = ((lean_object*)(l_tacticDecreasing__trivial___closed__1));
v___x_1113_ = ((lean_object*)(l_tacticDecreasing__trivial___closed__2));
v___x_1114_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1099_);
lean_ctor_set(v___x_1114_, 1, v___x_1113_);
v___x_1115_ = l_Lean_Syntax_node1(v___x_1099_, v___x_1112_, v___x_1114_);
lean_inc(v___x_1115_);
v___x_1116_ = l_Lean_Syntax_node1(v___x_1099_, v___x_1105_, v___x_1115_);
v___x_1117_ = l_Lean_Syntax_node1(v___x_1099_, v___x_1104_, v___x_1116_);
v___x_1118_ = l_Lean_Syntax_node1(v___x_1099_, v___x_1103_, v___x_1117_);
lean_inc_ref(v___x_1111_);
v___x_1119_ = l_Lean_Syntax_node2(v___x_1099_, v___x_1109_, v___x_1111_, v___x_1118_);
v___x_1120_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___closed__2));
v___x_1121_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___closed__3));
v___x_1122_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1122_, 0, v___x_1099_);
lean_ctor_set(v___x_1122_, 1, v___x_1121_);
v___x_1123_ = l_Lean_Syntax_node1(v___x_1099_, v___x_1120_, v___x_1122_);
v___x_1124_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__10));
v___x_1125_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1125_, 0, v___x_1099_);
lean_ctor_set(v___x_1125_, 1, v___x_1124_);
v___x_1126_ = l_Lean_Syntax_node3(v___x_1099_, v___x_1105_, v___x_1123_, v___x_1125_, v___x_1115_);
v___x_1127_ = l_Lean_Syntax_node1(v___x_1099_, v___x_1104_, v___x_1126_);
v___x_1128_ = l_Lean_Syntax_node1(v___x_1099_, v___x_1103_, v___x_1127_);
v___x_1129_ = l_Lean_Syntax_node2(v___x_1099_, v___x_1109_, v___x_1111_, v___x_1128_);
v___x_1130_ = l_Lean_Syntax_node2(v___x_1099_, v___x_1105_, v___x_1119_, v___x_1129_);
v___x_1131_ = l_Lean_Syntax_node2(v___x_1099_, v___x_1107_, v___x_1108_, v___x_1130_);
v___x_1132_ = l_Lean_Syntax_node1(v___x_1099_, v___x_1105_, v___x_1131_);
v___x_1133_ = l_Lean_Syntax_node1(v___x_1099_, v___x_1104_, v___x_1132_);
v___x_1134_ = l_Lean_Syntax_node1(v___x_1099_, v___x_1103_, v___x_1133_);
v___x_1135_ = l_Lean_Syntax_node2(v___x_1099_, v___x_1100_, v___x_1102_, v___x_1134_);
v___x_1136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1136_, 0, v___x_1135_);
lean_ctor_set(v___x_1136_, 1, v_a_1092_);
return v___x_1136_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___boxed(lean_object* v_x_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_){
_start:
{
lean_object* v_res_1140_; 
v_res_1140_ = l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1(v_x_1137_, v_a_1138_, v_a_1139_);
lean_dec_ref(v_a_1138_);
return v_res_1140_;
}
}
lean_object* runtime_initialize_Init_WF(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_WFTactics(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_WF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_WFTactics(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
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
res = runtime_initialize_Init_WFTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_WFTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_WFTactics(builtin);
}
#ifdef __cplusplus
}
#endif

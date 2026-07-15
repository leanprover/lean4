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
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__67_value)}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__69 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__69_value;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__69_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__70 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__70_value;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__68_value),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__70_value)}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__71 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__71_value;
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "WellFoundedRelation.rel"};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__72 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__72_value;
static lean_once_cell_t l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__73_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__73;
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "WellFoundedRelation"};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__74 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__74_value;
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rel"};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__75 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__75_value;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__76_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__74_value),LEAN_SCALAR_PTR_LITERAL(247, 146, 95, 132, 177, 137, 153, 47)}};
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__76_value_aux_0),((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__75_value),LEAN_SCALAR_PTR_LITERAL(149, 61, 97, 242, 68, 92, 238, 81)}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__76 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__76_value;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__76_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__77 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__77_value;
static const lean_ctor_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__78_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__77_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__78 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__78_value;
static const lean_string_object l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__79 = (const lean_object*)&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__79_value;
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
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__73(void){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_170_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__72));
v___x_171_ = l_String_toRawSubstring_x27(v___x_170_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1(lean_object* v_x_184_, lean_object* v_a_185_, lean_object* v_a_186_){
_start:
{
lean_object* v___x_187_; uint8_t v___x_188_; 
v___x_187_ = ((lean_object*)(l_tacticSimp__wf___closed__1));
v___x_188_ = l_Lean_Syntax_isOfKind(v_x_184_, v___x_187_);
if (v___x_188_ == 0)
{
lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_189_ = lean_box(1);
v___x_190_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_190_, 0, v___x_189_);
lean_ctor_set(v___x_190_, 1, v_a_186_);
return v___x_190_;
}
else
{
lean_object* v_quotContext_191_; lean_object* v_currMacroScope_192_; lean_object* v_ref_193_; uint8_t v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v_quotContext_191_ = lean_ctor_get(v_a_185_, 1);
v_currMacroScope_192_ = lean_ctor_get(v_a_185_, 2);
v_ref_193_ = lean_ctor_get(v_a_185_, 5);
v___x_194_ = 0;
v___x_195_ = l_Lean_SourceInfo_fromRef(v_ref_193_, v___x_194_);
v___x_196_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__4));
v___x_197_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__5));
lean_inc_n(v___x_195_, 35);
v___x_198_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_198_, 0, v___x_195_);
lean_ctor_set(v___x_198_, 1, v___x_197_);
v___x_199_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__7));
v___x_200_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__9));
v___x_201_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__11));
v___x_202_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__12));
v___x_203_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__13));
v___x_204_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_204_, 0, v___x_195_);
lean_ctor_set(v___x_204_, 1, v___x_202_);
v___x_205_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__15));
v___x_206_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__17));
v___x_207_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__19));
v___x_208_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__20));
v___x_209_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_209_, 0, v___x_195_);
lean_ctor_set(v___x_209_, 1, v___x_208_);
v___x_210_ = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__22, &l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__22_once, _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__22);
v___x_211_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__23));
lean_inc_n(v_currMacroScope_192_, 9);
lean_inc_n(v_quotContext_191_, 9);
v___x_212_ = l_Lean_addMacroScope(v_quotContext_191_, v___x_211_, v_currMacroScope_192_);
v___x_213_ = lean_box(0);
v___x_214_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_214_, 0, v___x_195_);
lean_ctor_set(v___x_214_, 1, v___x_210_);
lean_ctor_set(v___x_214_, 2, v___x_212_);
lean_ctor_set(v___x_214_, 3, v___x_213_);
lean_inc_ref(v___x_209_);
v___x_215_ = l_Lean_Syntax_node2(v___x_195_, v___x_207_, v___x_209_, v___x_214_);
v___x_216_ = l_Lean_Syntax_node1(v___x_195_, v___x_206_, v___x_215_);
v___x_217_ = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__25, &l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__25_once, _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__25);
v___x_218_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__26));
v___x_219_ = l_Lean_addMacroScope(v_quotContext_191_, v___x_218_, v_currMacroScope_192_);
v___x_220_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_220_, 0, v___x_195_);
lean_ctor_set(v___x_220_, 1, v___x_217_);
lean_ctor_set(v___x_220_, 2, v___x_219_);
lean_ctor_set(v___x_220_, 3, v___x_213_);
v___x_221_ = l_Lean_Syntax_node2(v___x_195_, v___x_207_, v___x_209_, v___x_220_);
v___x_222_ = l_Lean_Syntax_node1(v___x_195_, v___x_206_, v___x_221_);
v___x_223_ = l_Lean_Syntax_node2(v___x_195_, v___x_201_, v___x_216_, v___x_222_);
v___x_224_ = l_Lean_Syntax_node1(v___x_195_, v___x_205_, v___x_223_);
v___x_225_ = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__27, &l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__27_once, _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__27);
v___x_226_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_226_, 0, v___x_195_);
lean_ctor_set(v___x_226_, 1, v___x_201_);
lean_ctor_set(v___x_226_, 2, v___x_225_);
v___x_227_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__28));
v___x_228_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_228_, 0, v___x_195_);
lean_ctor_set(v___x_228_, 1, v___x_227_);
v___x_229_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__30));
v___x_230_ = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__32, &l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__32_once, _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__32);
v___x_231_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__33));
v___x_232_ = l_Lean_addMacroScope(v_quotContext_191_, v___x_231_, v_currMacroScope_192_);
v___x_233_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__35));
v___x_234_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_234_, 0, v___x_195_);
lean_ctor_set(v___x_234_, 1, v___x_230_);
lean_ctor_set(v___x_234_, 2, v___x_232_);
lean_ctor_set(v___x_234_, 3, v___x_233_);
lean_inc_ref_n(v___x_226_, 16);
v___x_235_ = l_Lean_Syntax_node3(v___x_195_, v___x_229_, v___x_226_, v___x_226_, v___x_234_);
v___x_236_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__36));
v___x_237_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_237_, 0, v___x_195_);
lean_ctor_set(v___x_237_, 1, v___x_236_);
v___x_238_ = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__38, &l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__38_once, _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__38);
v___x_239_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__39));
v___x_240_ = l_Lean_addMacroScope(v_quotContext_191_, v___x_239_, v_currMacroScope_192_);
v___x_241_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__43));
v___x_242_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_242_, 0, v___x_195_);
lean_ctor_set(v___x_242_, 1, v___x_238_);
lean_ctor_set(v___x_242_, 2, v___x_240_);
lean_ctor_set(v___x_242_, 3, v___x_241_);
v___x_243_ = l_Lean_Syntax_node3(v___x_195_, v___x_229_, v___x_226_, v___x_226_, v___x_242_);
v___x_244_ = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__45, &l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__45_once, _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__45);
v___x_245_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__48));
v___x_246_ = l_Lean_addMacroScope(v_quotContext_191_, v___x_245_, v_currMacroScope_192_);
v___x_247_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__52));
v___x_248_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_248_, 0, v___x_195_);
lean_ctor_set(v___x_248_, 1, v___x_244_);
lean_ctor_set(v___x_248_, 2, v___x_246_);
lean_ctor_set(v___x_248_, 3, v___x_247_);
v___x_249_ = l_Lean_Syntax_node3(v___x_195_, v___x_229_, v___x_226_, v___x_226_, v___x_248_);
v___x_250_ = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__54, &l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__54_once, _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__54);
v___x_251_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__55));
v___x_252_ = l_Lean_addMacroScope(v_quotContext_191_, v___x_251_, v_currMacroScope_192_);
v___x_253_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__57));
v___x_254_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_254_, 0, v___x_195_);
lean_ctor_set(v___x_254_, 1, v___x_250_);
lean_ctor_set(v___x_254_, 2, v___x_252_);
lean_ctor_set(v___x_254_, 3, v___x_253_);
v___x_255_ = l_Lean_Syntax_node3(v___x_195_, v___x_229_, v___x_226_, v___x_226_, v___x_254_);
v___x_256_ = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__59, &l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__59_once, _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__59);
v___x_257_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__60));
v___x_258_ = l_Lean_addMacroScope(v_quotContext_191_, v___x_257_, v_currMacroScope_192_);
v___x_259_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__62));
v___x_260_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_260_, 0, v___x_195_);
lean_ctor_set(v___x_260_, 1, v___x_256_);
lean_ctor_set(v___x_260_, 2, v___x_258_);
lean_ctor_set(v___x_260_, 3, v___x_259_);
v___x_261_ = l_Lean_Syntax_node3(v___x_195_, v___x_229_, v___x_226_, v___x_226_, v___x_260_);
v___x_262_ = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__64, &l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__64_once, _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__64);
v___x_263_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__67));
v___x_264_ = l_Lean_addMacroScope(v_quotContext_191_, v___x_263_, v_currMacroScope_192_);
v___x_265_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__71));
v___x_266_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_266_, 0, v___x_195_);
lean_ctor_set(v___x_266_, 1, v___x_262_);
lean_ctor_set(v___x_266_, 2, v___x_264_);
lean_ctor_set(v___x_266_, 3, v___x_265_);
v___x_267_ = l_Lean_Syntax_node3(v___x_195_, v___x_229_, v___x_226_, v___x_226_, v___x_266_);
v___x_268_ = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__73, &l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__73_once, _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__73);
v___x_269_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__76));
v___x_270_ = l_Lean_addMacroScope(v_quotContext_191_, v___x_269_, v_currMacroScope_192_);
v___x_271_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__78));
v___x_272_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_272_, 0, v___x_195_);
lean_ctor_set(v___x_272_, 1, v___x_268_);
lean_ctor_set(v___x_272_, 2, v___x_270_);
lean_ctor_set(v___x_272_, 3, v___x_271_);
v___x_273_ = l_Lean_Syntax_node3(v___x_195_, v___x_229_, v___x_226_, v___x_226_, v___x_272_);
v___x_274_ = lean_unsigned_to_nat(13u);
v___x_275_ = lean_mk_empty_array_with_capacity(v___x_274_);
v___x_276_ = lean_array_push(v___x_275_, v___x_235_);
lean_inc_ref_n(v___x_237_, 5);
v___x_277_ = lean_array_push(v___x_276_, v___x_237_);
v___x_278_ = lean_array_push(v___x_277_, v___x_243_);
v___x_279_ = lean_array_push(v___x_278_, v___x_237_);
v___x_280_ = lean_array_push(v___x_279_, v___x_249_);
v___x_281_ = lean_array_push(v___x_280_, v___x_237_);
v___x_282_ = lean_array_push(v___x_281_, v___x_255_);
v___x_283_ = lean_array_push(v___x_282_, v___x_237_);
v___x_284_ = lean_array_push(v___x_283_, v___x_261_);
v___x_285_ = lean_array_push(v___x_284_, v___x_237_);
v___x_286_ = lean_array_push(v___x_285_, v___x_267_);
v___x_287_ = lean_array_push(v___x_286_, v___x_237_);
v___x_288_ = lean_array_push(v___x_287_, v___x_273_);
v___x_289_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_289_, 0, v___x_195_);
lean_ctor_set(v___x_289_, 1, v___x_201_);
lean_ctor_set(v___x_289_, 2, v___x_288_);
v___x_290_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__79));
v___x_291_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_291_, 0, v___x_195_);
lean_ctor_set(v___x_291_, 1, v___x_290_);
v___x_292_ = l_Lean_Syntax_node3(v___x_195_, v___x_201_, v___x_228_, v___x_289_, v___x_291_);
v___x_293_ = l_Lean_Syntax_node6(v___x_195_, v___x_203_, v___x_204_, v___x_224_, v___x_226_, v___x_226_, v___x_292_, v___x_226_);
v___x_294_ = l_Lean_Syntax_node1(v___x_195_, v___x_201_, v___x_293_);
v___x_295_ = l_Lean_Syntax_node1(v___x_195_, v___x_200_, v___x_294_);
v___x_296_ = l_Lean_Syntax_node1(v___x_195_, v___x_199_, v___x_295_);
v___x_297_ = l_Lean_Syntax_node2(v___x_195_, v___x_196_, v___x_198_, v___x_296_);
v___x_298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_298_, 0, v___x_297_);
lean_ctor_set(v___x_298_, 1, v_a_186_);
return v___x_298_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___boxed(lean_object* v_x_299_, lean_object* v_a_300_, lean_object* v_a_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1(v_x_299_, v_a_300_, v_a_301_);
lean_dec_ref(v_a_300_);
return v_res_302_;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__4(void){
_start:
{
lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_323_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__3));
v___x_324_ = l_String_toRawSubstring_x27(v___x_323_);
return v___x_324_;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__8(void){
_start:
{
lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_329_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__7));
v___x_330_ = l_String_toRawSubstring_x27(v___x_329_);
return v___x_330_;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__13(void){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_340_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__12));
v___x_341_ = l_String_toRawSubstring_x27(v___x_340_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticClean__wf__1(lean_object* v_x_344_, lean_object* v_a_345_, lean_object* v_a_346_){
_start:
{
lean_object* v___x_347_; uint8_t v___x_348_; 
v___x_347_ = ((lean_object*)(l_tacticClean__wf___closed__1));
v___x_348_ = l_Lean_Syntax_isOfKind(v_x_344_, v___x_347_);
if (v___x_348_ == 0)
{
lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_349_ = lean_box(1);
v___x_350_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_350_, 0, v___x_349_);
lean_ctor_set(v___x_350_, 1, v_a_346_);
return v___x_350_;
}
else
{
lean_object* v_quotContext_351_; lean_object* v_currMacroScope_352_; lean_object* v_ref_353_; uint8_t v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v_quotContext_351_ = lean_ctor_get(v_a_345_, 1);
v_currMacroScope_352_ = lean_ctor_get(v_a_345_, 2);
v_ref_353_ = lean_ctor_get(v_a_345_, 5);
v___x_354_ = 0;
v___x_355_ = l_Lean_SourceInfo_fromRef(v_ref_353_, v___x_354_);
v___x_356_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__12));
v___x_357_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__13));
lean_inc_n(v___x_355_, 40);
v___x_358_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_358_, 0, v___x_355_);
lean_ctor_set(v___x_358_, 1, v___x_356_);
v___x_359_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__15));
v___x_360_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__11));
v___x_361_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__17));
v___x_362_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__19));
v___x_363_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__20));
v___x_364_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_364_, 0, v___x_355_);
lean_ctor_set(v___x_364_, 1, v___x_363_);
v___x_365_ = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__22, &l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__22_once, _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__22);
v___x_366_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__23));
lean_inc_n(v_currMacroScope_352_, 12);
lean_inc_n(v_quotContext_351_, 12);
v___x_367_ = l_Lean_addMacroScope(v_quotContext_351_, v___x_366_, v_currMacroScope_352_);
v___x_368_ = lean_box(0);
v___x_369_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_369_, 0, v___x_355_);
lean_ctor_set(v___x_369_, 1, v___x_365_);
lean_ctor_set(v___x_369_, 2, v___x_367_);
lean_ctor_set(v___x_369_, 3, v___x_368_);
lean_inc_ref(v___x_364_);
v___x_370_ = l_Lean_Syntax_node2(v___x_355_, v___x_362_, v___x_364_, v___x_369_);
v___x_371_ = l_Lean_Syntax_node1(v___x_355_, v___x_361_, v___x_370_);
v___x_372_ = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__25, &l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__25_once, _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__25);
v___x_373_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__26));
v___x_374_ = l_Lean_addMacroScope(v_quotContext_351_, v___x_373_, v_currMacroScope_352_);
v___x_375_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_375_, 0, v___x_355_);
lean_ctor_set(v___x_375_, 1, v___x_372_);
lean_ctor_set(v___x_375_, 2, v___x_374_);
lean_ctor_set(v___x_375_, 3, v___x_368_);
v___x_376_ = l_Lean_Syntax_node2(v___x_355_, v___x_362_, v___x_364_, v___x_375_);
v___x_377_ = l_Lean_Syntax_node1(v___x_355_, v___x_361_, v___x_376_);
v___x_378_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__1));
v___x_379_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__2));
v___x_380_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_380_, 0, v___x_355_);
lean_ctor_set(v___x_380_, 1, v___x_379_);
v___x_381_ = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__4, &l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__4_once, _init_l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__4);
v___x_382_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__5));
v___x_383_ = l_Lean_addMacroScope(v_quotContext_351_, v___x_382_, v_currMacroScope_352_);
v___x_384_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_384_, 0, v___x_355_);
lean_ctor_set(v___x_384_, 1, v___x_381_);
lean_ctor_set(v___x_384_, 2, v___x_383_);
lean_ctor_set(v___x_384_, 3, v___x_368_);
v___x_385_ = l_Lean_Syntax_node2(v___x_355_, v___x_378_, v___x_380_, v___x_384_);
v___x_386_ = l_Lean_Syntax_node1(v___x_355_, v___x_361_, v___x_385_);
v___x_387_ = l_Lean_Syntax_node3(v___x_355_, v___x_360_, v___x_371_, v___x_377_, v___x_386_);
v___x_388_ = l_Lean_Syntax_node1(v___x_355_, v___x_359_, v___x_387_);
v___x_389_ = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__27, &l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__27_once, _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__27);
v___x_390_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_390_, 0, v___x_355_);
lean_ctor_set(v___x_390_, 1, v___x_360_);
lean_ctor_set(v___x_390_, 2, v___x_389_);
v___x_391_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__6));
v___x_392_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_392_, 0, v___x_355_);
lean_ctor_set(v___x_392_, 1, v___x_391_);
v___x_393_ = l_Lean_Syntax_node1(v___x_355_, v___x_360_, v___x_392_);
v___x_394_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__28));
v___x_395_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_395_, 0, v___x_355_);
lean_ctor_set(v___x_395_, 1, v___x_394_);
v___x_396_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__30));
v___x_397_ = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__32, &l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__32_once, _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__32);
v___x_398_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__33));
v___x_399_ = l_Lean_addMacroScope(v_quotContext_351_, v___x_398_, v_currMacroScope_352_);
v___x_400_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__35));
v___x_401_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_401_, 0, v___x_355_);
lean_ctor_set(v___x_401_, 1, v___x_397_);
lean_ctor_set(v___x_401_, 2, v___x_399_);
lean_ctor_set(v___x_401_, 3, v___x_400_);
lean_inc_ref_n(v___x_390_, 19);
v___x_402_ = l_Lean_Syntax_node3(v___x_355_, v___x_396_, v___x_390_, v___x_390_, v___x_401_);
v___x_403_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__36));
v___x_404_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_404_, 0, v___x_355_);
lean_ctor_set(v___x_404_, 1, v___x_403_);
v___x_405_ = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__38, &l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__38_once, _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__38);
v___x_406_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__39));
v___x_407_ = l_Lean_addMacroScope(v_quotContext_351_, v___x_406_, v_currMacroScope_352_);
v___x_408_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__43));
v___x_409_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_409_, 0, v___x_355_);
lean_ctor_set(v___x_409_, 1, v___x_405_);
lean_ctor_set(v___x_409_, 2, v___x_407_);
lean_ctor_set(v___x_409_, 3, v___x_408_);
v___x_410_ = l_Lean_Syntax_node3(v___x_355_, v___x_396_, v___x_390_, v___x_390_, v___x_409_);
v___x_411_ = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__45, &l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__45_once, _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__45);
v___x_412_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__48));
v___x_413_ = l_Lean_addMacroScope(v_quotContext_351_, v___x_412_, v_currMacroScope_352_);
v___x_414_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__52));
v___x_415_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_415_, 0, v___x_355_);
lean_ctor_set(v___x_415_, 1, v___x_411_);
lean_ctor_set(v___x_415_, 2, v___x_413_);
lean_ctor_set(v___x_415_, 3, v___x_414_);
v___x_416_ = l_Lean_Syntax_node3(v___x_355_, v___x_396_, v___x_390_, v___x_390_, v___x_415_);
v___x_417_ = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__54, &l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__54_once, _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__54);
v___x_418_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__55));
v___x_419_ = l_Lean_addMacroScope(v_quotContext_351_, v___x_418_, v_currMacroScope_352_);
v___x_420_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__57));
v___x_421_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_421_, 0, v___x_355_);
lean_ctor_set(v___x_421_, 1, v___x_417_);
lean_ctor_set(v___x_421_, 2, v___x_419_);
lean_ctor_set(v___x_421_, 3, v___x_420_);
v___x_422_ = l_Lean_Syntax_node3(v___x_355_, v___x_396_, v___x_390_, v___x_390_, v___x_421_);
v___x_423_ = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__59, &l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__59_once, _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__59);
v___x_424_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__60));
v___x_425_ = l_Lean_addMacroScope(v_quotContext_351_, v___x_424_, v_currMacroScope_352_);
v___x_426_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__62));
v___x_427_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_427_, 0, v___x_355_);
lean_ctor_set(v___x_427_, 1, v___x_423_);
lean_ctor_set(v___x_427_, 2, v___x_425_);
lean_ctor_set(v___x_427_, 3, v___x_426_);
v___x_428_ = l_Lean_Syntax_node3(v___x_355_, v___x_396_, v___x_390_, v___x_390_, v___x_427_);
v___x_429_ = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__64, &l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__64_once, _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__64);
v___x_430_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__67));
v___x_431_ = l_Lean_addMacroScope(v_quotContext_351_, v___x_430_, v_currMacroScope_352_);
v___x_432_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__71));
v___x_433_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_433_, 0, v___x_355_);
lean_ctor_set(v___x_433_, 1, v___x_429_);
lean_ctor_set(v___x_433_, 2, v___x_431_);
lean_ctor_set(v___x_433_, 3, v___x_432_);
v___x_434_ = l_Lean_Syntax_node3(v___x_355_, v___x_396_, v___x_390_, v___x_390_, v___x_433_);
v___x_435_ = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__73, &l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__73_once, _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__73);
v___x_436_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__76));
v___x_437_ = l_Lean_addMacroScope(v_quotContext_351_, v___x_436_, v_currMacroScope_352_);
v___x_438_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__78));
v___x_439_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_439_, 0, v___x_355_);
lean_ctor_set(v___x_439_, 1, v___x_435_);
lean_ctor_set(v___x_439_, 2, v___x_437_);
lean_ctor_set(v___x_439_, 3, v___x_438_);
v___x_440_ = l_Lean_Syntax_node3(v___x_355_, v___x_396_, v___x_390_, v___x_390_, v___x_439_);
v___x_441_ = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__8, &l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__8_once, _init_l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__8);
v___x_442_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__9));
v___x_443_ = l_Lean_addMacroScope(v_quotContext_351_, v___x_442_, v_currMacroScope_352_);
v___x_444_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__11));
v___x_445_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_445_, 0, v___x_355_);
lean_ctor_set(v___x_445_, 1, v___x_441_);
lean_ctor_set(v___x_445_, 2, v___x_443_);
lean_ctor_set(v___x_445_, 3, v___x_444_);
v___x_446_ = l_Lean_Syntax_node3(v___x_355_, v___x_396_, v___x_390_, v___x_390_, v___x_445_);
v___x_447_ = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__13, &l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__13_once, _init_l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__13);
v___x_448_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__14));
v___x_449_ = l_Lean_addMacroScope(v_quotContext_351_, v___x_448_, v_currMacroScope_352_);
v___x_450_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_450_, 0, v___x_355_);
lean_ctor_set(v___x_450_, 1, v___x_447_);
lean_ctor_set(v___x_450_, 2, v___x_449_);
lean_ctor_set(v___x_450_, 3, v___x_368_);
v___x_451_ = l_Lean_Syntax_node3(v___x_355_, v___x_396_, v___x_390_, v___x_390_, v___x_450_);
v___x_452_ = lean_unsigned_to_nat(17u);
v___x_453_ = lean_mk_empty_array_with_capacity(v___x_452_);
v___x_454_ = lean_array_push(v___x_453_, v___x_402_);
lean_inc_ref_n(v___x_404_, 7);
v___x_455_ = lean_array_push(v___x_454_, v___x_404_);
v___x_456_ = lean_array_push(v___x_455_, v___x_410_);
v___x_457_ = lean_array_push(v___x_456_, v___x_404_);
v___x_458_ = lean_array_push(v___x_457_, v___x_416_);
v___x_459_ = lean_array_push(v___x_458_, v___x_404_);
v___x_460_ = lean_array_push(v___x_459_, v___x_422_);
v___x_461_ = lean_array_push(v___x_460_, v___x_404_);
v___x_462_ = lean_array_push(v___x_461_, v___x_428_);
v___x_463_ = lean_array_push(v___x_462_, v___x_404_);
v___x_464_ = lean_array_push(v___x_463_, v___x_434_);
v___x_465_ = lean_array_push(v___x_464_, v___x_404_);
v___x_466_ = lean_array_push(v___x_465_, v___x_440_);
v___x_467_ = lean_array_push(v___x_466_, v___x_404_);
v___x_468_ = lean_array_push(v___x_467_, v___x_446_);
v___x_469_ = lean_array_push(v___x_468_, v___x_404_);
v___x_470_ = lean_array_push(v___x_469_, v___x_451_);
v___x_471_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_471_, 0, v___x_355_);
lean_ctor_set(v___x_471_, 1, v___x_360_);
lean_ctor_set(v___x_471_, 2, v___x_470_);
v___x_472_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__79));
v___x_473_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_473_, 0, v___x_355_);
lean_ctor_set(v___x_473_, 1, v___x_472_);
v___x_474_ = l_Lean_Syntax_node3(v___x_355_, v___x_360_, v___x_395_, v___x_471_, v___x_473_);
v___x_475_ = l_Lean_Syntax_node6(v___x_355_, v___x_357_, v___x_358_, v___x_388_, v___x_390_, v___x_393_, v___x_474_, v___x_390_);
v___x_476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_476_, 0, v___x_475_);
lean_ctor_set(v___x_476_, 1, v_a_346_);
return v___x_476_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___boxed(lean_object* v_x_477_, lean_object* v_a_478_, lean_object* v_a_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l___aux__Init__WFTactics______macroRules__tacticClean__wf__1(v_x_477_, v_a_478_, v_a_479_);
lean_dec_ref(v_a_478_);
return v_res_480_;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__6(void){
_start:
{
lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_507_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__5));
v___x_508_ = l_String_toRawSubstring_x27(v___x_507_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1(lean_object* v_x_519_, lean_object* v_a_520_, lean_object* v_a_521_){
_start:
{
lean_object* v___x_522_; uint8_t v___x_523_; 
v___x_522_ = ((lean_object*)(l_tacticDecreasing__trivial___closed__1));
v___x_523_ = l_Lean_Syntax_isOfKind(v_x_519_, v___x_522_);
if (v___x_523_ == 0)
{
lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_524_ = lean_box(1);
v___x_525_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_525_, 0, v___x_524_);
lean_ctor_set(v___x_525_, 1, v_a_521_);
return v___x_525_;
}
else
{
lean_object* v_quotContext_526_; lean_object* v_currMacroScope_527_; lean_object* v_ref_528_; uint8_t v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v_quotContext_526_ = lean_ctor_get(v_a_520_, 1);
v_currMacroScope_527_ = lean_ctor_get(v_a_520_, 2);
v_ref_528_ = lean_ctor_get(v_a_520_, 5);
v___x_529_ = 0;
v___x_530_ = l_Lean_SourceInfo_fromRef(v_ref_528_, v___x_529_);
v___x_531_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__1));
v___x_532_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__3));
v___x_533_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__4));
lean_inc_n(v___x_530_, 22);
v___x_534_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_534_, 0, v___x_530_);
lean_ctor_set(v___x_534_, 1, v___x_533_);
v___x_535_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__7));
v___x_536_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__9));
v___x_537_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__11));
v___x_538_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__12));
v___x_539_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__13));
v___x_540_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_540_, 0, v___x_530_);
lean_ctor_set(v___x_540_, 1, v___x_538_);
v___x_541_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__15));
v___x_542_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__17));
v___x_543_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__19));
v___x_544_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__20));
v___x_545_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_545_, 0, v___x_530_);
lean_ctor_set(v___x_545_, 1, v___x_544_);
v___x_546_ = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__6, &l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__6_once, _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__6);
v___x_547_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__7));
lean_inc_n(v_currMacroScope_527_, 2);
lean_inc_n(v_quotContext_526_, 2);
v___x_548_ = l_Lean_addMacroScope(v_quotContext_526_, v___x_547_, v_currMacroScope_527_);
v___x_549_ = lean_box(0);
v___x_550_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_550_, 0, v___x_530_);
lean_ctor_set(v___x_550_, 1, v___x_546_);
lean_ctor_set(v___x_550_, 2, v___x_548_);
lean_ctor_set(v___x_550_, 3, v___x_549_);
v___x_551_ = l_Lean_Syntax_node2(v___x_530_, v___x_543_, v___x_545_, v___x_550_);
v___x_552_ = l_Lean_Syntax_node1(v___x_530_, v___x_542_, v___x_551_);
v___x_553_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__1));
v___x_554_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__2));
v___x_555_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_555_, 0, v___x_530_);
lean_ctor_set(v___x_555_, 1, v___x_554_);
v___x_556_ = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__4, &l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__4_once, _init_l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__4);
v___x_557_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__5));
v___x_558_ = l_Lean_addMacroScope(v_quotContext_526_, v___x_557_, v_currMacroScope_527_);
v___x_559_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_559_, 0, v___x_530_);
lean_ctor_set(v___x_559_, 1, v___x_556_);
lean_ctor_set(v___x_559_, 2, v___x_558_);
lean_ctor_set(v___x_559_, 3, v___x_549_);
v___x_560_ = l_Lean_Syntax_node2(v___x_530_, v___x_553_, v___x_555_, v___x_559_);
v___x_561_ = l_Lean_Syntax_node1(v___x_530_, v___x_542_, v___x_560_);
v___x_562_ = l_Lean_Syntax_node2(v___x_530_, v___x_537_, v___x_552_, v___x_561_);
v___x_563_ = l_Lean_Syntax_node1(v___x_530_, v___x_541_, v___x_562_);
v___x_564_ = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__27, &l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__27_once, _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__27);
v___x_565_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_565_, 0, v___x_530_);
lean_ctor_set(v___x_565_, 1, v___x_537_);
lean_ctor_set(v___x_565_, 2, v___x_564_);
lean_inc_ref_n(v___x_565_, 3);
v___x_566_ = l_Lean_Syntax_node6(v___x_530_, v___x_539_, v___x_540_, v___x_563_, v___x_565_, v___x_565_, v___x_565_, v___x_565_);
v___x_567_ = l_Lean_Syntax_node1(v___x_530_, v___x_537_, v___x_566_);
v___x_568_ = l_Lean_Syntax_node1(v___x_530_, v___x_536_, v___x_567_);
v___x_569_ = l_Lean_Syntax_node1(v___x_530_, v___x_535_, v___x_568_);
v___x_570_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__8));
v___x_571_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_571_, 0, v___x_530_);
lean_ctor_set(v___x_571_, 1, v___x_570_);
v___x_572_ = l_Lean_Syntax_node3(v___x_530_, v___x_532_, v___x_534_, v___x_569_, v___x_571_);
v___x_573_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__9));
v___x_574_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_574_, 0, v___x_530_);
lean_ctor_set(v___x_574_, 1, v___x_573_);
v___x_575_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__10));
v___x_576_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__11));
v___x_577_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_577_, 0, v___x_530_);
lean_ctor_set(v___x_577_, 1, v___x_575_);
v___x_578_ = l_Lean_Syntax_node1(v___x_530_, v___x_576_, v___x_577_);
v___x_579_ = l_Lean_Syntax_node3(v___x_530_, v___x_531_, v___x_572_, v___x_574_, v___x_578_);
v___x_580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_580_, 0, v___x_579_);
lean_ctor_set(v___x_580_, 1, v_a_521_);
return v___x_580_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___boxed(lean_object* v_x_581_, lean_object* v_a_582_, lean_object* v_a_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1(v_x_581_, v_a_582_, v_a_583_);
lean_dec_ref(v_a_582_);
return v_res_584_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__2(lean_object* v_x_591_, lean_object* v_a_592_, lean_object* v_a_593_){
_start:
{
lean_object* v___x_594_; uint8_t v___x_595_; 
v___x_594_ = ((lean_object*)(l_tacticDecreasing__trivial___closed__1));
v___x_595_ = l_Lean_Syntax_isOfKind(v_x_591_, v___x_594_);
if (v___x_595_ == 0)
{
lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_596_ = lean_box(1);
v___x_597_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_597_, 0, v___x_596_);
lean_ctor_set(v___x_597_, 1, v_a_593_);
return v___x_597_;
}
else
{
lean_object* v_ref_598_; uint8_t v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
v_ref_598_ = lean_ctor_get(v_a_592_, 5);
v___x_599_ = 0;
v___x_600_ = l_Lean_SourceInfo_fromRef(v_ref_598_, v___x_599_);
v___x_601_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__2___closed__0));
v___x_602_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__2___closed__1));
lean_inc_n(v___x_600_, 3);
v___x_603_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_603_, 0, v___x_600_);
lean_ctor_set(v___x_603_, 1, v___x_601_);
v___x_604_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__15));
v___x_605_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__11));
v___x_606_ = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__27, &l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__27_once, _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__27);
v___x_607_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_607_, 0, v___x_600_);
lean_ctor_set(v___x_607_, 1, v___x_605_);
lean_ctor_set(v___x_607_, 2, v___x_606_);
v___x_608_ = l_Lean_Syntax_node1(v___x_600_, v___x_604_, v___x_607_);
v___x_609_ = l_Lean_Syntax_node2(v___x_600_, v___x_602_, v___x_603_, v___x_608_);
v___x_610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_610_, 0, v___x_609_);
lean_ctor_set(v___x_610_, 1, v_a_593_);
return v___x_610_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__2___boxed(lean_object* v_x_611_, lean_object* v_a_612_, lean_object* v_a_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__2(v_x_611_, v_a_612_, v_a_613_);
lean_dec_ref(v_a_612_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3(lean_object* v_x_621_, lean_object* v_a_622_, lean_object* v_a_623_){
_start:
{
lean_object* v___x_624_; uint8_t v___x_625_; 
v___x_624_ = ((lean_object*)(l_tacticDecreasing__trivial___closed__1));
v___x_625_ = l_Lean_Syntax_isOfKind(v_x_621_, v___x_624_);
if (v___x_625_ == 0)
{
lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_626_ = lean_box(1);
v___x_627_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_627_, 0, v___x_626_);
lean_ctor_set(v___x_627_, 1, v_a_623_);
return v___x_627_;
}
else
{
lean_object* v_ref_628_; uint8_t v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v_ref_628_ = lean_ctor_get(v_a_622_, 5);
v___x_629_ = 0;
v___x_630_ = l_Lean_SourceInfo_fromRef(v_ref_628_, v___x_629_);
v___x_631_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___closed__0));
v___x_632_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___closed__1));
lean_inc(v___x_630_);
v___x_633_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_633_, 0, v___x_630_);
lean_ctor_set(v___x_633_, 1, v___x_631_);
v___x_634_ = l_Lean_Syntax_node1(v___x_630_, v___x_632_, v___x_633_);
v___x_635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_635_, 0, v___x_634_);
lean_ctor_set(v___x_635_, 1, v_a_623_);
return v___x_635_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___boxed(lean_object* v_x_636_, lean_object* v_a_637_, lean_object* v_a_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3(v_x_636_, v_a_637_, v_a_638_);
lean_dec_ref(v_a_637_);
return v_res_639_;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__5(void){
_start:
{
lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_665_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__4));
v___x_666_ = l_String_toRawSubstring_x27(v___x_665_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1(lean_object* v_x_678_, lean_object* v_a_679_, lean_object* v_a_680_){
_start:
{
lean_object* v___x_681_; uint8_t v___x_682_; 
v___x_681_ = ((lean_object*)(l_tacticDecreasing__trivial__pre__omega___closed__1));
v___x_682_ = l_Lean_Syntax_isOfKind(v_x_678_, v___x_681_);
if (v___x_682_ == 0)
{
lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_683_ = lean_box(1);
v___x_684_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_684_, 0, v___x_683_);
lean_ctor_set(v___x_684_, 1, v_a_680_);
return v___x_684_;
}
else
{
lean_object* v_quotContext_685_; lean_object* v_currMacroScope_686_; lean_object* v_ref_687_; uint8_t v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
v_quotContext_685_ = lean_ctor_get(v_a_679_, 1);
v_currMacroScope_686_ = lean_ctor_get(v_a_679_, 2);
v_ref_687_ = lean_ctor_get(v_a_679_, 5);
v___x_688_ = 0;
v___x_689_ = l_Lean_SourceInfo_fromRef(v_ref_687_, v___x_688_);
v___x_690_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__1));
v___x_691_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__11));
v___x_692_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__2));
v___x_693_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__3));
lean_inc_n(v___x_689_, 7);
v___x_694_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_694_, 0, v___x_689_);
lean_ctor_set(v___x_694_, 1, v___x_692_);
v___x_695_ = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__5, &l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__5_once, _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__5);
v___x_696_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__7));
lean_inc(v_currMacroScope_686_);
lean_inc(v_quotContext_685_);
v___x_697_ = l_Lean_addMacroScope(v_quotContext_685_, v___x_696_, v_currMacroScope_686_);
v___x_698_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__9));
v___x_699_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_699_, 0, v___x_689_);
lean_ctor_set(v___x_699_, 1, v___x_695_);
lean_ctor_set(v___x_699_, 2, v___x_697_);
lean_ctor_set(v___x_699_, 3, v___x_698_);
v___x_700_ = l_Lean_Syntax_node2(v___x_689_, v___x_693_, v___x_694_, v___x_699_);
v___x_701_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__10));
v___x_702_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_702_, 0, v___x_689_);
lean_ctor_set(v___x_702_, 1, v___x_701_);
v___x_703_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___closed__0));
v___x_704_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___closed__1));
v___x_705_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_705_, 0, v___x_689_);
lean_ctor_set(v___x_705_, 1, v___x_703_);
v___x_706_ = l_Lean_Syntax_node1(v___x_689_, v___x_704_, v___x_705_);
v___x_707_ = l_Lean_Syntax_node3(v___x_689_, v___x_691_, v___x_700_, v___x_702_, v___x_706_);
v___x_708_ = l_Lean_Syntax_node1(v___x_689_, v___x_690_, v___x_707_);
v___x_709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_709_, 0, v___x_708_);
lean_ctor_set(v___x_709_, 1, v_a_680_);
return v___x_709_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___boxed(lean_object* v_x_710_, lean_object* v_a_711_, lean_object* v_a_712_){
_start:
{
lean_object* v_res_713_; 
v_res_713_ = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1(v_x_710_, v_a_711_, v_a_712_);
lean_dec_ref(v_a_711_);
return v_res_713_;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__1(void){
_start:
{
lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_715_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__0));
v___x_716_ = l_String_toRawSubstring_x27(v___x_715_);
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2(lean_object* v_x_727_, lean_object* v_a_728_, lean_object* v_a_729_){
_start:
{
lean_object* v___x_730_; uint8_t v___x_731_; 
v___x_730_ = ((lean_object*)(l_tacticDecreasing__trivial__pre__omega___closed__1));
v___x_731_ = l_Lean_Syntax_isOfKind(v_x_727_, v___x_730_);
if (v___x_731_ == 0)
{
lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_732_ = lean_box(1);
v___x_733_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_733_, 0, v___x_732_);
lean_ctor_set(v___x_733_, 1, v_a_729_);
return v___x_733_;
}
else
{
lean_object* v_quotContext_734_; lean_object* v_currMacroScope_735_; lean_object* v_ref_736_; uint8_t v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
v_quotContext_734_ = lean_ctor_get(v_a_728_, 1);
v_currMacroScope_735_ = lean_ctor_get(v_a_728_, 2);
v_ref_736_ = lean_ctor_get(v_a_728_, 5);
v___x_737_ = 0;
v___x_738_ = l_Lean_SourceInfo_fromRef(v_ref_736_, v___x_737_);
v___x_739_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__1));
v___x_740_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__11));
v___x_741_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__2));
v___x_742_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__3));
lean_inc_n(v___x_738_, 7);
v___x_743_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_743_, 0, v___x_738_);
lean_ctor_set(v___x_743_, 1, v___x_741_);
v___x_744_ = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__1, &l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__1_once, _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__1);
v___x_745_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__3));
lean_inc(v_currMacroScope_735_);
lean_inc(v_quotContext_734_);
v___x_746_ = l_Lean_addMacroScope(v_quotContext_734_, v___x_745_, v_currMacroScope_735_);
v___x_747_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__5));
v___x_748_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_748_, 0, v___x_738_);
lean_ctor_set(v___x_748_, 1, v___x_744_);
lean_ctor_set(v___x_748_, 2, v___x_746_);
lean_ctor_set(v___x_748_, 3, v___x_747_);
v___x_749_ = l_Lean_Syntax_node2(v___x_738_, v___x_742_, v___x_743_, v___x_748_);
v___x_750_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__10));
v___x_751_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_751_, 0, v___x_738_);
lean_ctor_set(v___x_751_, 1, v___x_750_);
v___x_752_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___closed__0));
v___x_753_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___closed__1));
v___x_754_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_754_, 0, v___x_738_);
lean_ctor_set(v___x_754_, 1, v___x_752_);
v___x_755_ = l_Lean_Syntax_node1(v___x_738_, v___x_753_, v___x_754_);
v___x_756_ = l_Lean_Syntax_node3(v___x_738_, v___x_740_, v___x_749_, v___x_751_, v___x_755_);
v___x_757_ = l_Lean_Syntax_node1(v___x_738_, v___x_739_, v___x_756_);
v___x_758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_758_, 0, v___x_757_);
lean_ctor_set(v___x_758_, 1, v_a_729_);
return v___x_758_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___boxed(lean_object* v_x_759_, lean_object* v_a_760_, lean_object* v_a_761_){
_start:
{
lean_object* v_res_762_; 
v_res_762_ = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2(v_x_759_, v_a_760_, v_a_761_);
lean_dec_ref(v_a_760_);
return v_res_762_;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__1(void){
_start:
{
lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_764_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__0));
v___x_765_ = l_String_toRawSubstring_x27(v___x_764_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3(lean_object* v_x_776_, lean_object* v_a_777_, lean_object* v_a_778_){
_start:
{
lean_object* v___x_779_; uint8_t v___x_780_; 
v___x_779_ = ((lean_object*)(l_tacticDecreasing__trivial__pre__omega___closed__1));
v___x_780_ = l_Lean_Syntax_isOfKind(v_x_776_, v___x_779_);
if (v___x_780_ == 0)
{
lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_781_ = lean_box(1);
v___x_782_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_782_, 0, v___x_781_);
lean_ctor_set(v___x_782_, 1, v_a_778_);
return v___x_782_;
}
else
{
lean_object* v_quotContext_783_; lean_object* v_currMacroScope_784_; lean_object* v_ref_785_; uint8_t v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; 
v_quotContext_783_ = lean_ctor_get(v_a_777_, 1);
v_currMacroScope_784_ = lean_ctor_get(v_a_777_, 2);
v_ref_785_ = lean_ctor_get(v_a_777_, 5);
v___x_786_ = 0;
v___x_787_ = l_Lean_SourceInfo_fromRef(v_ref_785_, v___x_786_);
v___x_788_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__1));
v___x_789_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__11));
v___x_790_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__2));
v___x_791_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__3));
lean_inc_n(v___x_787_, 7);
v___x_792_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_792_, 0, v___x_787_);
lean_ctor_set(v___x_792_, 1, v___x_790_);
v___x_793_ = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__1, &l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__1_once, _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__1);
v___x_794_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__3));
lean_inc(v_currMacroScope_784_);
lean_inc(v_quotContext_783_);
v___x_795_ = l_Lean_addMacroScope(v_quotContext_783_, v___x_794_, v_currMacroScope_784_);
v___x_796_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__5));
v___x_797_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_797_, 0, v___x_787_);
lean_ctor_set(v___x_797_, 1, v___x_793_);
lean_ctor_set(v___x_797_, 2, v___x_795_);
lean_ctor_set(v___x_797_, 3, v___x_796_);
v___x_798_ = l_Lean_Syntax_node2(v___x_787_, v___x_791_, v___x_792_, v___x_797_);
v___x_799_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__10));
v___x_800_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_800_, 0, v___x_787_);
lean_ctor_set(v___x_800_, 1, v___x_799_);
v___x_801_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___closed__0));
v___x_802_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___closed__1));
v___x_803_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_803_, 0, v___x_787_);
lean_ctor_set(v___x_803_, 1, v___x_801_);
v___x_804_ = l_Lean_Syntax_node1(v___x_787_, v___x_802_, v___x_803_);
v___x_805_ = l_Lean_Syntax_node3(v___x_787_, v___x_789_, v___x_798_, v___x_800_, v___x_804_);
v___x_806_ = l_Lean_Syntax_node1(v___x_787_, v___x_788_, v___x_805_);
v___x_807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_807_, 0, v___x_806_);
lean_ctor_set(v___x_807_, 1, v_a_778_);
return v___x_807_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___boxed(lean_object* v_x_808_, lean_object* v_a_809_, lean_object* v_a_810_){
_start:
{
lean_object* v_res_811_; 
v_res_811_ = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3(v_x_808_, v_a_809_, v_a_810_);
lean_dec_ref(v_a_809_);
return v_res_811_;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__9(void){
_start:
{
lean_object* v___x_853_; lean_object* v___x_854_; 
v___x_853_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__8));
v___x_854_ = l_String_toRawSubstring_x27(v___x_853_);
return v___x_854_;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__16(void){
_start:
{
lean_object* v___x_868_; lean_object* v___x_869_; 
v___x_868_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__15));
v___x_869_ = l_String_toRawSubstring_x27(v___x_868_);
return v___x_869_;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__22(void){
_start:
{
lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_882_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__21));
v___x_883_ = l_String_toRawSubstring_x27(v___x_882_);
return v___x_883_;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__28(void){
_start:
{
lean_object* v___x_896_; lean_object* v___x_897_; 
v___x_896_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__27));
v___x_897_ = l_String_toRawSubstring_x27(v___x_896_);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1(lean_object* v_x_918_, lean_object* v_a_919_, lean_object* v_a_920_){
_start:
{
lean_object* v___x_921_; uint8_t v___x_922_; 
v___x_921_ = ((lean_object*)(l_tacticDecreasing__with___00__closed__1));
lean_inc(v_x_918_);
v___x_922_ = l_Lean_Syntax_isOfKind(v_x_918_, v___x_921_);
if (v___x_922_ == 0)
{
lean_object* v___x_923_; lean_object* v___x_924_; 
lean_dec(v_x_918_);
v___x_923_ = lean_box(1);
v___x_924_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_924_, 0, v___x_923_);
lean_ctor_set(v___x_924_, 1, v_a_920_);
return v___x_924_;
}
else
{
lean_object* v_quotContext_925_; lean_object* v_currMacroScope_926_; lean_object* v_ref_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; uint8_t v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
v_quotContext_925_ = lean_ctor_get(v_a_919_, 1);
v_currMacroScope_926_ = lean_ctor_get(v_a_919_, 2);
v_ref_927_ = lean_ctor_get(v_a_919_, 5);
v___x_928_ = lean_unsigned_to_nat(1u);
v___x_929_ = l_Lean_Syntax_getArg(v_x_918_, v___x_928_);
lean_dec(v_x_918_);
v___x_930_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__7));
v___x_931_ = 0;
v___x_932_ = l_Lean_SourceInfo_fromRef(v_ref_927_, v___x_931_);
v___x_933_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__3));
v___x_934_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__4));
lean_inc_n(v___x_932_, 82);
v___x_935_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_935_, 0, v___x_932_);
lean_ctor_set(v___x_935_, 1, v___x_934_);
v___x_936_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__9));
v___x_937_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__11));
v___x_938_ = ((lean_object*)(l_tacticClean__wf___closed__1));
v___x_939_ = ((lean_object*)(l_tacticClean__wf___closed__2));
v___x_940_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_940_, 0, v___x_932_);
lean_ctor_set(v___x_940_, 1, v___x_939_);
v___x_941_ = l_Lean_Syntax_node1(v___x_932_, v___x_938_, v___x_940_);
v___x_942_ = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__27, &l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__27_once, _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__27);
v___x_943_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_943_, 0, v___x_932_);
lean_ctor_set(v___x_943_, 1, v___x_937_);
lean_ctor_set(v___x_943_, 2, v___x_942_);
v___x_944_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__4));
v___x_945_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__5));
v___x_946_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_946_, 0, v___x_932_);
lean_ctor_set(v___x_946_, 1, v___x_945_);
v___x_947_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__12));
v___x_948_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__13));
v___x_949_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_949_, 0, v___x_932_);
lean_ctor_set(v___x_949_, 1, v___x_947_);
v___x_950_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__15));
lean_inc_ref_n(v___x_943_, 8);
v___x_951_ = l_Lean_Syntax_node1(v___x_932_, v___x_950_, v___x_943_);
v___x_952_ = l_Lean_Syntax_node6(v___x_932_, v___x_948_, v___x_949_, v___x_951_, v___x_943_, v___x_943_, v___x_943_, v___x_943_);
v___x_953_ = l_Lean_Syntax_node1(v___x_932_, v___x_937_, v___x_952_);
v___x_954_ = l_Lean_Syntax_node1(v___x_932_, v___x_936_, v___x_953_);
v___x_955_ = l_Lean_Syntax_node1(v___x_932_, v___x_930_, v___x_954_);
v___x_956_ = l_Lean_Syntax_node2(v___x_932_, v___x_944_, v___x_946_, v___x_955_);
v___x_957_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__1));
v___x_958_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__2));
v___x_959_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_959_, 0, v___x_932_);
lean_ctor_set(v___x_959_, 1, v___x_958_);
v___x_960_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__3));
v___x_961_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__4));
v___x_962_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_962_, 0, v___x_932_);
lean_ctor_set(v___x_962_, 1, v___x_960_);
v___x_963_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__6));
v___x_964_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__7));
v___x_965_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_965_, 0, v___x_932_);
lean_ctor_set(v___x_965_, 1, v___x_964_);
v___x_966_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__2));
v___x_967_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__3));
v___x_968_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_968_, 0, v___x_932_);
lean_ctor_set(v___x_968_, 1, v___x_966_);
v___x_969_ = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__9, &l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__9_once, _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__9);
v___x_970_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__12));
lean_inc_n(v_currMacroScope_926_, 4);
lean_inc_n(v_quotContext_925_, 4);
v___x_971_ = l_Lean_addMacroScope(v_quotContext_925_, v___x_970_, v_currMacroScope_926_);
v___x_972_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__14));
v___x_973_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_973_, 0, v___x_932_);
lean_ctor_set(v___x_973_, 1, v___x_969_);
lean_ctor_set(v___x_973_, 2, v___x_971_);
lean_ctor_set(v___x_973_, 3, v___x_972_);
lean_inc_ref_n(v___x_968_, 3);
v___x_974_ = l_Lean_Syntax_node2(v___x_932_, v___x_967_, v___x_968_, v___x_973_);
v___x_975_ = l_Lean_Syntax_node1(v___x_932_, v___x_937_, v___x_974_);
v___x_976_ = l_Lean_Syntax_node1(v___x_932_, v___x_936_, v___x_975_);
v___x_977_ = l_Lean_Syntax_node1(v___x_932_, v___x_930_, v___x_976_);
lean_inc_ref_n(v___x_965_, 6);
v___x_978_ = l_Lean_Syntax_node2(v___x_932_, v___x_963_, v___x_965_, v___x_977_);
v___x_979_ = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__16, &l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__16_once, _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__16);
v___x_980_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__18));
v___x_981_ = l_Lean_addMacroScope(v_quotContext_925_, v___x_980_, v_currMacroScope_926_);
v___x_982_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__20));
v___x_983_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_983_, 0, v___x_932_);
lean_ctor_set(v___x_983_, 1, v___x_979_);
lean_ctor_set(v___x_983_, 2, v___x_981_);
lean_ctor_set(v___x_983_, 3, v___x_982_);
v___x_984_ = l_Lean_Syntax_node2(v___x_932_, v___x_967_, v___x_968_, v___x_983_);
v___x_985_ = l_Lean_Syntax_node1(v___x_932_, v___x_937_, v___x_984_);
v___x_986_ = l_Lean_Syntax_node1(v___x_932_, v___x_936_, v___x_985_);
v___x_987_ = l_Lean_Syntax_node1(v___x_932_, v___x_930_, v___x_986_);
v___x_988_ = l_Lean_Syntax_node2(v___x_932_, v___x_963_, v___x_965_, v___x_987_);
v___x_989_ = l_Lean_Syntax_node2(v___x_932_, v___x_937_, v___x_978_, v___x_988_);
lean_inc_ref_n(v___x_962_, 2);
v___x_990_ = l_Lean_Syntax_node2(v___x_932_, v___x_961_, v___x_962_, v___x_989_);
v___x_991_ = l_Lean_Syntax_node1(v___x_932_, v___x_937_, v___x_990_);
v___x_992_ = l_Lean_Syntax_node1(v___x_932_, v___x_936_, v___x_991_);
v___x_993_ = l_Lean_Syntax_node1(v___x_932_, v___x_930_, v___x_992_);
v___x_994_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__8));
v___x_995_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_995_, 0, v___x_932_);
lean_ctor_set(v___x_995_, 1, v___x_994_);
lean_inc_ref_n(v___x_995_, 2);
lean_inc_ref_n(v___x_935_, 2);
v___x_996_ = l_Lean_Syntax_node3(v___x_932_, v___x_933_, v___x_935_, v___x_993_, v___x_995_);
v___x_997_ = l_Lean_Syntax_node1(v___x_932_, v___x_937_, v___x_996_);
v___x_998_ = l_Lean_Syntax_node1(v___x_932_, v___x_936_, v___x_997_);
v___x_999_ = l_Lean_Syntax_node1(v___x_932_, v___x_930_, v___x_998_);
lean_inc_ref(v___x_959_);
v___x_1000_ = l_Lean_Syntax_node2(v___x_932_, v___x_957_, v___x_959_, v___x_999_);
v___x_1001_ = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__22, &l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__22_once, _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__22);
v___x_1002_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__24));
v___x_1003_ = l_Lean_addMacroScope(v_quotContext_925_, v___x_1002_, v_currMacroScope_926_);
v___x_1004_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__26));
v___x_1005_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1005_, 0, v___x_932_);
lean_ctor_set(v___x_1005_, 1, v___x_1001_);
lean_ctor_set(v___x_1005_, 2, v___x_1003_);
lean_ctor_set(v___x_1005_, 3, v___x_1004_);
v___x_1006_ = l_Lean_Syntax_node2(v___x_932_, v___x_967_, v___x_968_, v___x_1005_);
v___x_1007_ = l_Lean_Syntax_node1(v___x_932_, v___x_937_, v___x_1006_);
v___x_1008_ = l_Lean_Syntax_node1(v___x_932_, v___x_936_, v___x_1007_);
v___x_1009_ = l_Lean_Syntax_node1(v___x_932_, v___x_930_, v___x_1008_);
v___x_1010_ = l_Lean_Syntax_node2(v___x_932_, v___x_963_, v___x_965_, v___x_1009_);
v___x_1011_ = lean_obj_once(&l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__28, &l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__28_once, _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__28);
v___x_1012_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__29));
v___x_1013_ = l_Lean_addMacroScope(v_quotContext_925_, v___x_1012_, v_currMacroScope_926_);
v___x_1014_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__31));
v___x_1015_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1015_, 0, v___x_932_);
lean_ctor_set(v___x_1015_, 1, v___x_1011_);
lean_ctor_set(v___x_1015_, 2, v___x_1013_);
lean_ctor_set(v___x_1015_, 3, v___x_1014_);
v___x_1016_ = l_Lean_Syntax_node2(v___x_932_, v___x_967_, v___x_968_, v___x_1015_);
v___x_1017_ = l_Lean_Syntax_node1(v___x_932_, v___x_937_, v___x_1016_);
v___x_1018_ = l_Lean_Syntax_node1(v___x_932_, v___x_936_, v___x_1017_);
v___x_1019_ = l_Lean_Syntax_node1(v___x_932_, v___x_930_, v___x_1018_);
v___x_1020_ = l_Lean_Syntax_node2(v___x_932_, v___x_963_, v___x_965_, v___x_1019_);
v___x_1021_ = l_Lean_Syntax_node2(v___x_932_, v___x_937_, v___x_1010_, v___x_1020_);
v___x_1022_ = l_Lean_Syntax_node2(v___x_932_, v___x_961_, v___x_962_, v___x_1021_);
v___x_1023_ = l_Lean_Syntax_node1(v___x_932_, v___x_937_, v___x_1022_);
v___x_1024_ = l_Lean_Syntax_node1(v___x_932_, v___x_936_, v___x_1023_);
v___x_1025_ = l_Lean_Syntax_node1(v___x_932_, v___x_930_, v___x_1024_);
v___x_1026_ = l_Lean_Syntax_node3(v___x_932_, v___x_933_, v___x_935_, v___x_1025_, v___x_995_);
v___x_1027_ = l_Lean_Syntax_node1(v___x_932_, v___x_937_, v___x_1026_);
v___x_1028_ = l_Lean_Syntax_node1(v___x_932_, v___x_936_, v___x_1027_);
v___x_1029_ = l_Lean_Syntax_node1(v___x_932_, v___x_930_, v___x_1028_);
v___x_1030_ = l_Lean_Syntax_node2(v___x_932_, v___x_957_, v___x_959_, v___x_1029_);
v___x_1031_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__10));
v___x_1032_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__11));
v___x_1033_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1033_, 0, v___x_932_);
lean_ctor_set(v___x_1033_, 1, v___x_1031_);
v___x_1034_ = l_Lean_Syntax_node1(v___x_932_, v___x_1032_, v___x_1033_);
v___x_1035_ = l_Lean_Syntax_node1(v___x_932_, v___x_937_, v___x_1034_);
v___x_1036_ = l_Lean_Syntax_node1(v___x_932_, v___x_936_, v___x_1035_);
v___x_1037_ = l_Lean_Syntax_node1(v___x_932_, v___x_930_, v___x_1036_);
v___x_1038_ = l_Lean_Syntax_node2(v___x_932_, v___x_963_, v___x_965_, v___x_1037_);
v___x_1039_ = l_Lean_Syntax_node2(v___x_932_, v___x_963_, v___x_965_, v___x_929_);
v___x_1040_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__32));
v___x_1041_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__33));
v___x_1042_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1042_, 0, v___x_932_);
lean_ctor_set(v___x_1042_, 1, v___x_1040_);
v___x_1043_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__35));
v___x_1044_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__36));
v___x_1045_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1045_, 0, v___x_932_);
lean_ctor_set(v___x_1045_, 1, v___x_1044_);
v___x_1046_ = l_Lean_Syntax_node1(v___x_932_, v___x_1043_, v___x_1045_);
v___x_1047_ = l_Lean_Syntax_node1(v___x_932_, v___x_937_, v___x_1046_);
v___x_1048_ = l_Lean_Syntax_node2(v___x_932_, v___x_1041_, v___x_1042_, v___x_1047_);
v___x_1049_ = l_Lean_Syntax_node1(v___x_932_, v___x_937_, v___x_1048_);
v___x_1050_ = l_Lean_Syntax_node1(v___x_932_, v___x_936_, v___x_1049_);
v___x_1051_ = l_Lean_Syntax_node1(v___x_932_, v___x_930_, v___x_1050_);
v___x_1052_ = l_Lean_Syntax_node2(v___x_932_, v___x_963_, v___x_965_, v___x_1051_);
v___x_1053_ = l_Lean_Syntax_node3(v___x_932_, v___x_937_, v___x_1038_, v___x_1039_, v___x_1052_);
v___x_1054_ = l_Lean_Syntax_node2(v___x_932_, v___x_961_, v___x_962_, v___x_1053_);
v___x_1055_ = lean_unsigned_to_nat(9u);
v___x_1056_ = lean_mk_empty_array_with_capacity(v___x_1055_);
v___x_1057_ = lean_array_push(v___x_1056_, v___x_941_);
v___x_1058_ = lean_array_push(v___x_1057_, v___x_943_);
v___x_1059_ = lean_array_push(v___x_1058_, v___x_956_);
v___x_1060_ = lean_array_push(v___x_1059_, v___x_943_);
v___x_1061_ = lean_array_push(v___x_1060_, v___x_1000_);
v___x_1062_ = lean_array_push(v___x_1061_, v___x_943_);
v___x_1063_ = lean_array_push(v___x_1062_, v___x_1030_);
v___x_1064_ = lean_array_push(v___x_1063_, v___x_943_);
v___x_1065_ = lean_array_push(v___x_1064_, v___x_1054_);
v___x_1066_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1066_, 0, v___x_932_);
lean_ctor_set(v___x_1066_, 1, v___x_937_);
lean_ctor_set(v___x_1066_, 2, v___x_1065_);
v___x_1067_ = l_Lean_Syntax_node1(v___x_932_, v___x_936_, v___x_1066_);
v___x_1068_ = l_Lean_Syntax_node1(v___x_932_, v___x_930_, v___x_1067_);
v___x_1069_ = l_Lean_Syntax_node3(v___x_932_, v___x_933_, v___x_935_, v___x_1068_, v___x_995_);
v___x_1070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1069_);
lean_ctor_set(v___x_1070_, 1, v_a_920_);
return v___x_1070_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___boxed(lean_object* v_x_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_){
_start:
{
lean_object* v_res_1074_; 
v_res_1074_ = l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1(v_x_1071_, v_a_1072_, v_a_1073_);
lean_dec_ref(v_a_1072_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1(lean_object* v_x_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_){
_start:
{
lean_object* v___x_1098_; uint8_t v___x_1099_; 
v___x_1098_ = ((lean_object*)(l_tacticDecreasing__tactic___closed__1));
v___x_1099_ = l_Lean_Syntax_isOfKind(v_x_1095_, v___x_1098_);
if (v___x_1099_ == 0)
{
lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___x_1100_ = lean_box(1);
v___x_1101_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1101_, 0, v___x_1100_);
lean_ctor_set(v___x_1101_, 1, v_a_1097_);
return v___x_1101_;
}
else
{
lean_object* v_ref_1102_; uint8_t v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; 
v_ref_1102_ = lean_ctor_get(v_a_1096_, 5);
v___x_1103_ = 0;
v___x_1104_ = l_Lean_SourceInfo_fromRef(v_ref_1102_, v___x_1103_);
v___x_1105_ = ((lean_object*)(l_tacticDecreasing__with___00__closed__1));
v___x_1106_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___closed__0));
lean_inc_n(v___x_1104_, 21);
v___x_1107_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1107_, 0, v___x_1104_);
lean_ctor_set(v___x_1107_, 1, v___x_1106_);
v___x_1108_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__7));
v___x_1109_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__9));
v___x_1110_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__11));
v___x_1111_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__3));
v___x_1112_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__4));
v___x_1113_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1113_, 0, v___x_1104_);
lean_ctor_set(v___x_1113_, 1, v___x_1111_);
v___x_1114_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__6));
v___x_1115_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__7));
v___x_1116_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1116_, 0, v___x_1104_);
lean_ctor_set(v___x_1116_, 1, v___x_1115_);
v___x_1117_ = ((lean_object*)(l_tacticDecreasing__trivial___closed__1));
v___x_1118_ = ((lean_object*)(l_tacticDecreasing__trivial___closed__2));
v___x_1119_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1104_);
lean_ctor_set(v___x_1119_, 1, v___x_1118_);
v___x_1120_ = l_Lean_Syntax_node1(v___x_1104_, v___x_1117_, v___x_1119_);
lean_inc(v___x_1120_);
v___x_1121_ = l_Lean_Syntax_node1(v___x_1104_, v___x_1110_, v___x_1120_);
v___x_1122_ = l_Lean_Syntax_node1(v___x_1104_, v___x_1109_, v___x_1121_);
v___x_1123_ = l_Lean_Syntax_node1(v___x_1104_, v___x_1108_, v___x_1122_);
lean_inc_ref(v___x_1116_);
v___x_1124_ = l_Lean_Syntax_node2(v___x_1104_, v___x_1114_, v___x_1116_, v___x_1123_);
v___x_1125_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___closed__2));
v___x_1126_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___closed__3));
v___x_1127_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1127_, 0, v___x_1104_);
lean_ctor_set(v___x_1127_, 1, v___x_1126_);
v___x_1128_ = l_Lean_Syntax_node1(v___x_1104_, v___x_1125_, v___x_1127_);
v___x_1129_ = ((lean_object*)(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__10));
v___x_1130_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1130_, 0, v___x_1104_);
lean_ctor_set(v___x_1130_, 1, v___x_1129_);
v___x_1131_ = l_Lean_Syntax_node3(v___x_1104_, v___x_1110_, v___x_1128_, v___x_1130_, v___x_1120_);
v___x_1132_ = l_Lean_Syntax_node1(v___x_1104_, v___x_1109_, v___x_1131_);
v___x_1133_ = l_Lean_Syntax_node1(v___x_1104_, v___x_1108_, v___x_1132_);
v___x_1134_ = l_Lean_Syntax_node2(v___x_1104_, v___x_1114_, v___x_1116_, v___x_1133_);
v___x_1135_ = l_Lean_Syntax_node2(v___x_1104_, v___x_1110_, v___x_1124_, v___x_1134_);
v___x_1136_ = l_Lean_Syntax_node2(v___x_1104_, v___x_1112_, v___x_1113_, v___x_1135_);
v___x_1137_ = l_Lean_Syntax_node1(v___x_1104_, v___x_1110_, v___x_1136_);
v___x_1138_ = l_Lean_Syntax_node1(v___x_1104_, v___x_1109_, v___x_1137_);
v___x_1139_ = l_Lean_Syntax_node1(v___x_1104_, v___x_1108_, v___x_1138_);
v___x_1140_ = l_Lean_Syntax_node2(v___x_1104_, v___x_1105_, v___x_1107_, v___x_1139_);
v___x_1141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1141_, 0, v___x_1140_);
lean_ctor_set(v___x_1141_, 1, v_a_1097_);
return v___x_1141_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___boxed(lean_object* v_x_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_){
_start:
{
lean_object* v_res_1145_; 
v_res_1145_ = l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1(v_x_1142_, v_a_1143_, v_a_1144_);
lean_dec_ref(v_a_1143_);
return v_res_1145_;
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

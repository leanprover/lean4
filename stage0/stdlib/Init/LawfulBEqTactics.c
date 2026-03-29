// Lean compiler output
// Module: Init.LawfulBEqTactics
// Imports: public import Init.Core import Init.Data.Bool import Init.ByCases import Init.Classical
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static const lean_string_object l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "DerivingHelpers"};
static const lean_object* l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__0 = (const lean_object*)&l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__0_value;
static const lean_string_object l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "tacticDeriving_ReflEq_tactic"};
static const lean_object* l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__1 = (const lean_object*)&l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__1_value;
static const lean_ctor_object l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(20, 45, 30, 199, 86, 148, 73, 212)}};
static const lean_ctor_object l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__2_value_aux_0),((lean_object*)&l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__1_value),LEAN_SCALAR_PTR_LITERAL(59, 102, 201, 20, 211, 124, 83, 120)}};
static const lean_object* l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__2 = (const lean_object*)&l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__2_value;
static const lean_string_object l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "deriving_ReflEq_tactic"};
static const lean_object* l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__3 = (const lean_object*)&l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__3_value;
static const lean_ctor_object l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__4 = (const lean_object*)&l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__4_value;
static const lean_ctor_object l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__2_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__4_value)}};
static const lean_object* l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__5 = (const lean_object*)&l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__5_value;
LEAN_EXPORT const lean_object* l_DerivingHelpers_tacticDeriving__ReflEq__tactic = (const lean_object*)&l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__5_value;
static const lean_string_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0 = (const lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value;
static const lean_string_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1 = (const lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value;
static const lean_string_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2 = (const lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value;
static const lean_string_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__3 = (const lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__3_value;
static const lean_ctor_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__4_value_aux_0),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__4_value_aux_1),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__4_value_aux_2),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(117, 253, 122, 28, 77, 248, 149, 120)}};
static const lean_object* l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__4 = (const lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__4_value;
static const lean_string_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__5 = (const lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__5_value;
static const lean_string_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__6 = (const lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__6_value;
static const lean_ctor_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__7_value_aux_0),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__7_value_aux_1),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__7_value_aux_2),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__7 = (const lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__7_value;
static const lean_string_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__8 = (const lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__8_value;
static const lean_ctor_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__9_value_aux_0),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__9_value_aux_1),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__9_value_aux_2),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__9 = (const lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__9_value;
static const lean_string_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__10 = (const lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__10_value;
static const lean_ctor_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__11 = (const lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__11_value;
static const lean_string_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "intro"};
static const lean_object* l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__12 = (const lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__12_value;
static const lean_ctor_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__13_value_aux_0),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__13_value_aux_1),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__13_value_aux_2),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(41, 145, 9, 18, 75, 146, 159, 78)}};
static const lean_object* l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__13 = (const lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__13_value;
static const lean_string_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__14 = (const lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__14_value;
static lean_once_cell_t l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__15;
static const lean_ctor_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__16 = (const lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__16_value;
static lean_once_cell_t l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__17;
static const lean_string_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "induction"};
static const lean_object* l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__18 = (const lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__18_value;
static const lean_ctor_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__19_value_aux_0),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__19_value_aux_1),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__19_value_aux_2),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(231, 196, 247, 144, 178, 6, 178, 16)}};
static const lean_object* l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__19 = (const lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__19_value;
static const lean_string_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "elimTarget"};
static const lean_object* l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__20 = (const lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__20_value;
static const lean_ctor_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__21_value_aux_0),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__21_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__21_value_aux_1),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__21_value_aux_2),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(136, 63, 46, 91, 99, 29, 205, 171)}};
static const lean_object* l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__21 = (const lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__21_value;
static const lean_string_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "allGoals"};
static const lean_object* l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__22 = (const lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__22_value;
static const lean_ctor_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__23_value_aux_0),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__23_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__23_value_aux_1),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__23_value_aux_2),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(105, 66, 138, 83, 251, 171, 29, 196)}};
static const lean_object* l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__23 = (const lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__23_value;
static const lean_string_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "all_goals"};
static const lean_object* l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__24 = (const lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__24_value;
static const lean_string_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__25 = (const lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__25_value;
static const lean_ctor_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__26_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__26_value_aux_0),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__26_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__26_value_aux_1),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__26_value_aux_2),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__25_value),LEAN_SCALAR_PTR_LITERAL(50, 13, 241, 145, 67, 153, 105, 177)}};
static const lean_object* l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__26 = (const lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__26_value;
static const lean_string_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__27 = (const lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__27_value;
static const lean_ctor_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__28_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__28_value_aux_0),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__28_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__28_value_aux_1),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__28_value_aux_2),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__27_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__28 = (const lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__28_value;
static const lean_string_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "only"};
static const lean_object* l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__29 = (const lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__29_value;
static const lean_string_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__30 = (const lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__30_value;
static const lean_string_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "simpLemma"};
static const lean_object* l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__31 = (const lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__31_value;
static const lean_ctor_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__32_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__32_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__32_value_aux_0),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__32_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__32_value_aux_1),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__32_value_aux_2),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__31_value),LEAN_SCALAR_PTR_LITERAL(38, 215, 101, 250, 181, 108, 118, 102)}};
static const lean_object* l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__32 = (const lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__32_value;
static const lean_string_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "BEq.refl"};
static const lean_object* l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__33 = (const lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__33_value;
static lean_once_cell_t l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__34;
static const lean_string_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "BEq"};
static const lean_object* l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__35 = (const lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__35_value;
static const lean_string_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "refl"};
static const lean_object* l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__36 = (const lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__36_value;
static const lean_ctor_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__37_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__35_value),LEAN_SCALAR_PTR_LITERAL(195, 188, 39, 55, 57, 152, 88, 223)}};
static const lean_ctor_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__37_value_aux_0),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__36_value),LEAN_SCALAR_PTR_LITERAL(52, 88, 160, 60, 208, 53, 173, 40)}};
static const lean_object* l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__37 = (const lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__37_value;
static const lean_ctor_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__37_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__38 = (const lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__38_value;
static const lean_ctor_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__38_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__39 = (const lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__39_value;
static const lean_string_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__40 = (const lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__40_value;
static const lean_string_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "simpPre"};
static const lean_object* l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__41 = (const lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__41_value;
static const lean_ctor_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__42_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__42_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__42_value_aux_0),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__42_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__42_value_aux_1),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__42_value_aux_2),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__41_value),LEAN_SCALAR_PTR_LITERAL(197, 59, 48, 6, 36, 81, 149, 152)}};
static const lean_object* l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__42 = (const lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__42_value;
static const lean_string_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "↓"};
static const lean_object* l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__43 = (const lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__43_value;
static const lean_string_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "reduceDIte"};
static const lean_object* l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__44 = (const lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__44_value;
static lean_once_cell_t l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__45;
static const lean_ctor_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__44_value),LEAN_SCALAR_PTR_LITERAL(30, 101, 22, 109, 248, 175, 82, 75)}};
static const lean_object* l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__46 = (const lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__46_value;
static const lean_string_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Bool.and_true"};
static const lean_object* l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__47 = (const lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__47_value;
static lean_once_cell_t l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__48_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__48;
static const lean_string_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__49 = (const lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__49_value;
static const lean_string_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "and_true"};
static const lean_object* l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__50 = (const lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__50_value;
static const lean_ctor_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__51_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__49_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__51_value_aux_0),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__50_value),LEAN_SCALAR_PTR_LITERAL(24, 213, 152, 164, 55, 55, 23, 67)}};
static const lean_object* l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__51 = (const lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__51_value;
static const lean_ctor_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__51_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__52 = (const lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__52_value;
static const lean_ctor_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__52_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__53 = (const lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__53_value;
static const lean_string_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "simpStar"};
static const lean_object* l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__54 = (const lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__54_value;
static const lean_ctor_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__55_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__55_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__55_value_aux_0),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__55_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__55_value_aux_1),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__55_value_aux_2),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__54_value),LEAN_SCALAR_PTR_LITERAL(125, 38, 251, 225, 228, 173, 11, 37)}};
static const lean_object* l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__55 = (const lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__55_value;
static const lean_string_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "*"};
static const lean_object* l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__56 = (const lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__56_value;
static const lean_string_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceBEq"};
static const lean_object* l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__57 = (const lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__57_value;
static lean_once_cell_t l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__58_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__58;
static const lean_ctor_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__57_value),LEAN_SCALAR_PTR_LITERAL(7, 43, 34, 163, 80, 156, 84, 109)}};
static const lean_object* l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__59 = (const lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__59_value;
static const lean_string_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "reduceCtorIdx"};
static const lean_object* l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__60 = (const lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__60_value;
static lean_once_cell_t l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__61_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__61;
static const lean_ctor_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__60_value),LEAN_SCALAR_PTR_LITERAL(47, 140, 108, 243, 19, 200, 28, 162)}};
static const lean_object* l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__62 = (const lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__62_value;
static const lean_string_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__63 = (const lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__63_value;
static const lean_string_object l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__64 = (const lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__64_value;
LEAN_EXPORT lean_object* l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_tacticDeriving__LawfulEq__tactic__step___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "tacticDeriving_LawfulEq_tactic_step"};
static const lean_object* l_tacticDeriving__LawfulEq__tactic__step___closed__0 = (const lean_object*)&l_tacticDeriving__LawfulEq__tactic__step___closed__0_value;
static const lean_ctor_object l_tacticDeriving__LawfulEq__tactic__step___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_tacticDeriving__LawfulEq__tactic__step___closed__0_value),LEAN_SCALAR_PTR_LITERAL(219, 88, 244, 182, 105, 175, 212, 80)}};
static const lean_object* l_tacticDeriving__LawfulEq__tactic__step___closed__1 = (const lean_object*)&l_tacticDeriving__LawfulEq__tactic__step___closed__1_value;
static const lean_string_object l_tacticDeriving__LawfulEq__tactic__step___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "deriving_LawfulEq_tactic_step"};
static const lean_object* l_tacticDeriving__LawfulEq__tactic__step___closed__2 = (const lean_object*)&l_tacticDeriving__LawfulEq__tactic__step___closed__2_value;
static const lean_ctor_object l_tacticDeriving__LawfulEq__tactic__step___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_tacticDeriving__LawfulEq__tactic__step___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_tacticDeriving__LawfulEq__tactic__step___closed__3 = (const lean_object*)&l_tacticDeriving__LawfulEq__tactic__step___closed__3_value;
static const lean_ctor_object l_tacticDeriving__LawfulEq__tactic__step___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_tacticDeriving__LawfulEq__tactic__step___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_tacticDeriving__LawfulEq__tactic__step___closed__3_value)}};
static const lean_object* l_tacticDeriving__LawfulEq__tactic__step___closed__4 = (const lean_object*)&l_tacticDeriving__LawfulEq__tactic__step___closed__4_value;
LEAN_EXPORT const lean_object* l_tacticDeriving__LawfulEq__tactic__step = (const lean_object*)&l_tacticDeriving__LawfulEq__tactic__step___closed__4_value;
static const lean_string_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "fail"};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__0 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__0_value;
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__1_value_aux_0),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__1_value_aux_1),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__1_value_aux_2),((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(251, 214, 242, 89, 226, 36, 213, 0)}};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__1 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__1_value;
static const lean_string_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__2 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__2_value;
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__3 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__3_value;
static const lean_string_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "\"deriving_LawfulEq_tactic_step failed\""};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__4 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__4_value;
LEAN_EXPORT lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "withReducible"};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__0 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__0_value;
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__1_value_aux_0),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__1_value_aux_1),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__1_value_aux_2),((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(197, 44, 223, 192, 8, 197, 146, 83)}};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__1 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__1_value;
static const lean_string_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "with_reducible"};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__2 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__2_value;
static const lean_string_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "change"};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__3 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__3_value;
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__4_value_aux_0),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__4_value_aux_1),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__4_value_aux_2),((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__3_value),LEAN_SCALAR_PTR_LITERAL(228, 221, 63, 213, 180, 29, 27, 230)}};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__4 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__4_value;
static const lean_string_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__5 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__5_value;
static const lean_string_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "arrow"};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__6 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__6_value;
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__7_value_aux_0),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__7_value_aux_1),((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__5_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__7_value_aux_2),((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__6_value),LEAN_SCALAR_PTR_LITERAL(182, 146, 143, 73, 122, 115, 5, 207)}};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__7 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__7_value;
static const lean_string_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "term_=_"};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__8 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__8_value;
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__8_value),LEAN_SCALAR_PTR_LITERAL(167, 251, 107, 62, 223, 239, 203, 78)}};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__9 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__9_value;
static const lean_string_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__10 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__10_value;
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__11_value_aux_0),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__11_value_aux_1),((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__5_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__11_value_aux_2),((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__10_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__11 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__11_value;
static const lean_string_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "dite"};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__12 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__12_value;
static lean_once_cell_t l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__13;
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__12_value),LEAN_SCALAR_PTR_LITERAL(137, 166, 197, 161, 68, 218, 116, 116)}};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__14 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__14_value;
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__14_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__15 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__15_value;
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__15_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__16 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__16_value;
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__17_value_aux_0),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__17_value_aux_1),((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__5_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__17_value_aux_2),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__17 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__17_value;
static const lean_string_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__18 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__18_value;
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__19_value_aux_0),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__19_value_aux_1),((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__5_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__19_value_aux_2),((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__18_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__19 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__19_value;
static const lean_string_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__20 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__20_value;
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__20_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__21 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__21_value;
static const lean_string_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__22 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__22_value;
static lean_once_cell_t l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__23;
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__24 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__24_value;
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__24_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__25 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__25_value;
static const lean_string_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "term_==_"};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__26 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__26_value;
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__26_value),LEAN_SCALAR_PTR_LITERAL(25, 251, 60, 160, 118, 54, 158, 27)}};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__27 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__27_value;
static const lean_string_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__28 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__28_value;
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__29_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__29_value_aux_0),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__29_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__29_value_aux_1),((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__5_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__29_value_aux_2),((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__28_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__29 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__29_value;
static const lean_string_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__30 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__30_value;
static const lean_string_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=="};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__31 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__31_value;
static const lean_string_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "="};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__32 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__32_value;
static const lean_string_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__33 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__33_value;
static lean_once_cell_t l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__34;
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__33_value),LEAN_SCALAR_PTR_LITERAL(235, 97, 249, 134, 197, 220, 12, 91)}};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__35 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__35_value;
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__36_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__49_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__36_value_aux_0),((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__33_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__36 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__36_value;
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__36_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__37 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__37_value;
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__37_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__38 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__38_value;
static const lean_string_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "→"};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__39 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__39_value;
static const lean_string_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "refine"};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__40 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__40_value;
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__41_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__41_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__41_value_aux_0),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__41_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__41_value_aux_1),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__41_value_aux_2),((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__40_value),LEAN_SCALAR_PTR_LITERAL(49, 130, 130, 160, 131, 48, 178, 245)}};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__41 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__41_value;
static const lean_string_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "DerivingHelpers.deriving_lawful_beq_helper_dep"};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__42 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__42_value;
static lean_once_cell_t l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__43_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__43;
static const lean_string_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "deriving_lawful_beq_helper_dep"};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__44 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__44_value;
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__45_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(20, 45, 30, 199, 86, 148, 73, 212)}};
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__45_value_aux_0),((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__44_value),LEAN_SCALAR_PTR_LITERAL(144, 218, 200, 98, 181, 248, 224, 118)}};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__45 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__45_value;
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__45_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__46 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__46_value;
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__46_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__47 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__47_value;
static const lean_string_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "syntheticHole"};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__48 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__48_value;
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__49_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__49_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__49_value_aux_0),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__49_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__49_value_aux_1),((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__5_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__49_value_aux_2),((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__48_value),LEAN_SCALAR_PTR_LITERAL(218, 189, 67, 60, 211, 196, 112, 165)}};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__49 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__49_value;
static const lean_string_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\?"};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__50 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__50_value;
static const lean_string_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cdot"};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__51 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__51_value;
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__52_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__52_value_aux_0),((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__51_value),LEAN_SCALAR_PTR_LITERAL(238, 151, 138, 49, 249, 18, 254, 242)}};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__52 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__52_value;
static const lean_string_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "cdotTk"};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__53 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__53_value;
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__54_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__54_value_aux_0),((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__53_value),LEAN_SCALAR_PTR_LITERAL(117, 126, 44, 217, 38, 3, 69, 145)}};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__54 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__54_value;
static const lean_string_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 1, .m_data = "·"};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__55 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__55_value;
static const lean_string_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "solveTactic"};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__56 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__56_value;
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__57_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__57_value_aux_0),((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__56_value),LEAN_SCALAR_PTR_LITERAL(203, 93, 240, 221, 8, 79, 216, 244)}};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__57 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__57_value;
static const lean_string_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "solve"};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__58 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__58_value;
static const lean_string_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "group"};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__59 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__59_value;
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__59_value),LEAN_SCALAR_PTR_LITERAL(206, 113, 20, 57, 188, 177, 187, 30)}};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__60 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__60_value;
static const lean_string_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "|"};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__61 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__61_value;
static const lean_string_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "applyAssumption"};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__62 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__62_value;
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__63_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__63_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__63_value_aux_0),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__63_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__63_value_aux_1),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__63_value_aux_2),((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__62_value),LEAN_SCALAR_PTR_LITERAL(6, 202, 232, 143, 104, 29, 235, 93)}};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__63 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__63_value;
static const lean_string_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "apply_assumption"};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__64 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__64_value;
static const lean_string_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "\"could not discharge eq_of_beq assumption\""};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__65 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__65_value;
static const lean_string_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__66 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__66_value;
static lean_once_cell_t l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__67_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__67;
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__66_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__68 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__68_value;
static const lean_string_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "cases"};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__69 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__69_value;
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__70_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__70_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__70_value_aux_0),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__70_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__70_value_aux_1),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__70_value_aux_2),((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__69_value),LEAN_SCALAR_PTR_LITERAL(197, 49, 98, 208, 150, 151, 163, 74)}};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__70 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__70_value;
static const lean_string_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "dsimp"};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__71 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__71_value;
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__72_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__72_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__72_value_aux_0),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__72_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__72_value_aux_1),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__72_value_aux_2),((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__71_value),LEAN_SCALAR_PTR_LITERAL(246, 53, 215, 155, 171, 182, 123, 76)}};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__72 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__72_value;
LEAN_EXPORT lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__24_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__0 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__0_value;
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__36_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__1 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__1_value;
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__2 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__2_value;
static const lean_string_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "DerivingHelpers.deriving_lawful_beq_helper_nd"};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__3 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__3_value;
static lean_once_cell_t l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__4;
static const lean_string_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "deriving_lawful_beq_helper_nd"};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__5 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__5_value;
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(20, 45, 30, 199, 86, 148, 73, 212)}};
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__6_value_aux_0),((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__5_value),LEAN_SCALAR_PTR_LITERAL(70, 187, 245, 31, 54, 78, 192, 202)}};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__6 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__6_value;
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__7 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__7_value;
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__7_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__8 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__8_value;
static const lean_string_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "subst"};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__9 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__9_value;
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__10_value_aux_0),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__10_value_aux_1),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__10_value_aux_2),((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__9_value),LEAN_SCALAR_PTR_LITERAL(72, 253, 96, 40, 175, 171, 7, 145)}};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__10 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__10_value;
LEAN_EXPORT lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "term_&&_"};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__0 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__0_value;
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(6, 195, 203, 117, 177, 125, 57, 22)}};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__1 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__1_value;
static const lean_string_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "&&"};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__2 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__2_value;
static const lean_string_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "DerivingHelpers.and_true_curry"};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__3 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__3_value;
static lean_once_cell_t l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__4;
static const lean_string_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "and_true_curry"};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__5 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__5_value;
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(20, 45, 30, 199, 86, 148, 73, 212)}};
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__6_value_aux_0),((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__5_value),LEAN_SCALAR_PTR_LITERAL(82, 127, 194, 200, 179, 233, 137, 241)}};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__6 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__6_value;
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__7 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__7_value;
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__7_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__8 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__8_value;
LEAN_EXPORT lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticRfl"};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__5___closed__0 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__5___closed__0_value;
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__5___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__5___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__5___closed__1_value_aux_0),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__5___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__5___closed__1_value_aux_1),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__5___closed__1_value_aux_2),((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(201, 188, 173, 198, 169, 252, 183, 45)}};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__5___closed__1 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__5___closed__1_value;
static const lean_string_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rfl"};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__5___closed__2 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__5___closed__2_value;
LEAN_EXPORT lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__5___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "seq1"};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__0 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__0_value;
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__1_value_aux_0),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__1_value_aux_1),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__1_value_aux_2),((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__0_value),LEAN_SCALAR_PTR_LITERAL(242, 140, 137, 56, 141, 11, 143, 117)}};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__1 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__1_value;
static const lean_string_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ";"};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__2 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__2_value;
static const lean_string_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "tacticTrivial"};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__3 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__3_value;
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__4_value_aux_0),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__4_value_aux_1),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__4_value_aux_2),((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__3_value),LEAN_SCALAR_PTR_LITERAL(91, 113, 211, 1, 53, 106, 100, 38)}};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__4 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__4_value;
static const lean_string_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "trivial"};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__5 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__5_value;
LEAN_EXPORT lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_tacticDeriving__LawfulEq__tactic___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "tacticDeriving_LawfulEq_tactic"};
static const lean_object* l_tacticDeriving__LawfulEq__tactic___closed__0 = (const lean_object*)&l_tacticDeriving__LawfulEq__tactic___closed__0_value;
static const lean_ctor_object l_tacticDeriving__LawfulEq__tactic___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_tacticDeriving__LawfulEq__tactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 236, 164, 161, 104, 237, 167, 171)}};
static const lean_object* l_tacticDeriving__LawfulEq__tactic___closed__1 = (const lean_object*)&l_tacticDeriving__LawfulEq__tactic___closed__1_value;
static const lean_string_object l_tacticDeriving__LawfulEq__tactic___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "deriving_LawfulEq_tactic"};
static const lean_object* l_tacticDeriving__LawfulEq__tactic___closed__2 = (const lean_object*)&l_tacticDeriving__LawfulEq__tactic___closed__2_value;
static const lean_ctor_object l_tacticDeriving__LawfulEq__tactic___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_tacticDeriving__LawfulEq__tactic___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_tacticDeriving__LawfulEq__tactic___closed__3 = (const lean_object*)&l_tacticDeriving__LawfulEq__tactic___closed__3_value;
static const lean_ctor_object l_tacticDeriving__LawfulEq__tactic___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_tacticDeriving__LawfulEq__tactic___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_tacticDeriving__LawfulEq__tactic___closed__3_value)}};
static const lean_object* l_tacticDeriving__LawfulEq__tactic___closed__4 = (const lean_object*)&l_tacticDeriving__LawfulEq__tactic___closed__4_value;
LEAN_EXPORT const lean_object* l_tacticDeriving__LawfulEq__tactic = (const lean_object*)&l_tacticDeriving__LawfulEq__tactic___closed__4_value;
static const lean_string_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "y"};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__0 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__0_value;
static lean_once_cell_t l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__1;
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(72, 55, 55, 9, 143, 73, 230, 150)}};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__2 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__2_value;
static const lean_string_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "tacticRepeat_"};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__3 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__3_value;
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__4_value_aux_0),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__4_value_aux_1),((lean_object*)&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__4_value_aux_2),((lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(149, 101, 42, 245, 144, 172, 68, 230)}};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__4 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__4_value;
static const lean_string_object l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "repeat"};
static const lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__5 = (const lean_object*)&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__5_value;
LEAN_EXPORT lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__15(void){
_start:
{
lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_47_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__14));
v___x_48_ = l_String_toRawSubstring_x27(v___x_47_);
return v___x_48_;
}
}
static lean_object* _init_l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__17(void){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = l_Array_mkArray0(lean_box(0));
return v___x_51_;
}
}
static lean_object* _init_l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__34(void){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_92_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__33));
v___x_93_ = l_String_toRawSubstring_x27(v___x_92_);
return v___x_93_;
}
}
static lean_object* _init_l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__45(void){
_start:
{
lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_114_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__44));
v___x_115_ = l_String_toRawSubstring_x27(v___x_114_);
return v___x_115_;
}
}
static lean_object* _init_l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__48(void){
_start:
{
lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_119_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__47));
v___x_120_ = l_String_toRawSubstring_x27(v___x_119_);
return v___x_120_;
}
}
static lean_object* _init_l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__58(void){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_140_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__57));
v___x_141_ = l_String_toRawSubstring_x27(v___x_140_);
return v___x_141_;
}
}
static lean_object* _init_l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__61(void){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_145_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__60));
v___x_146_ = l_String_toRawSubstring_x27(v___x_145_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1(lean_object* v_x_151_, lean_object* v_a_152_, lean_object* v_a_153_){
_start:
{
lean_object* v___x_154_; uint8_t v___x_155_; 
v___x_154_ = ((lean_object*)(l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__2));
v___x_155_ = l_Lean_Syntax_isOfKind(v_x_151_, v___x_154_);
if (v___x_155_ == 0)
{
lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_156_ = lean_box(1);
v___x_157_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_157_, 0, v___x_156_);
lean_ctor_set(v___x_157_, 1, v_a_153_);
return v___x_157_;
}
else
{
lean_object* v_quotContext_158_; lean_object* v_currMacroScope_159_; lean_object* v_ref_160_; uint8_t v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v_quotContext_158_ = lean_ctor_get(v_a_152_, 1);
v_currMacroScope_159_ = lean_ctor_get(v_a_152_, 2);
v_ref_160_ = lean_ctor_get(v_a_152_, 5);
v___x_161_ = 0;
v___x_162_ = l_Lean_SourceInfo_fromRef(v_ref_160_, v___x_161_);
v___x_163_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__4));
v___x_164_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__5));
lean_inc_n(v___x_162_, 44);
v___x_165_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_165_, 0, v___x_162_);
lean_ctor_set(v___x_165_, 1, v___x_164_);
v___x_166_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__7));
v___x_167_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__9));
v___x_168_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__11));
v___x_169_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__12));
v___x_170_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__13));
v___x_171_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_171_, 0, v___x_162_);
lean_ctor_set(v___x_171_, 1, v___x_169_);
v___x_172_ = lean_obj_once(&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__15, &l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__15_once, _init_l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__15);
v___x_173_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__16));
lean_inc_n(v_currMacroScope_159_, 6);
lean_inc_n(v_quotContext_158_, 6);
v___x_174_ = l_Lean_addMacroScope(v_quotContext_158_, v___x_173_, v_currMacroScope_159_);
v___x_175_ = lean_box(0);
v___x_176_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_176_, 0, v___x_162_);
lean_ctor_set(v___x_176_, 1, v___x_172_);
lean_ctor_set(v___x_176_, 2, v___x_174_);
lean_ctor_set(v___x_176_, 3, v___x_175_);
lean_inc_ref(v___x_176_);
v___x_177_ = l_Lean_Syntax_node1(v___x_162_, v___x_168_, v___x_176_);
v___x_178_ = l_Lean_Syntax_node2(v___x_162_, v___x_170_, v___x_171_, v___x_177_);
v___x_179_ = lean_obj_once(&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__17, &l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__17_once, _init_l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__17);
v___x_180_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_180_, 0, v___x_162_);
lean_ctor_set(v___x_180_, 1, v___x_168_);
lean_ctor_set(v___x_180_, 2, v___x_179_);
v___x_181_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__18));
v___x_182_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__19));
v___x_183_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_183_, 0, v___x_162_);
lean_ctor_set(v___x_183_, 1, v___x_181_);
v___x_184_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__21));
lean_inc_ref_n(v___x_180_, 17);
v___x_185_ = l_Lean_Syntax_node2(v___x_162_, v___x_184_, v___x_180_, v___x_176_);
v___x_186_ = l_Lean_Syntax_node1(v___x_162_, v___x_168_, v___x_185_);
v___x_187_ = l_Lean_Syntax_node5(v___x_162_, v___x_182_, v___x_183_, v___x_186_, v___x_180_, v___x_180_, v___x_180_);
v___x_188_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__23));
v___x_189_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__24));
v___x_190_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_190_, 0, v___x_162_);
lean_ctor_set(v___x_190_, 1, v___x_189_);
v___x_191_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__25));
v___x_192_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__26));
v___x_193_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_193_, 0, v___x_162_);
lean_ctor_set(v___x_193_, 1, v___x_191_);
v___x_194_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__28));
v___x_195_ = l_Lean_Syntax_node1(v___x_162_, v___x_194_, v___x_180_);
v___x_196_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__29));
v___x_197_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_197_, 0, v___x_162_);
lean_ctor_set(v___x_197_, 1, v___x_196_);
v___x_198_ = l_Lean_Syntax_node1(v___x_162_, v___x_168_, v___x_197_);
v___x_199_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__30));
v___x_200_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_200_, 0, v___x_162_);
lean_ctor_set(v___x_200_, 1, v___x_199_);
v___x_201_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__32));
v___x_202_ = lean_obj_once(&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__34, &l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__34_once, _init_l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__34);
v___x_203_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__37));
v___x_204_ = l_Lean_addMacroScope(v_quotContext_158_, v___x_203_, v_currMacroScope_159_);
v___x_205_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__39));
v___x_206_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_206_, 0, v___x_162_);
lean_ctor_set(v___x_206_, 1, v___x_202_);
lean_ctor_set(v___x_206_, 2, v___x_204_);
lean_ctor_set(v___x_206_, 3, v___x_205_);
v___x_207_ = l_Lean_Syntax_node3(v___x_162_, v___x_201_, v___x_180_, v___x_180_, v___x_206_);
v___x_208_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__40));
v___x_209_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_209_, 0, v___x_162_);
lean_ctor_set(v___x_209_, 1, v___x_208_);
v___x_210_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__42));
v___x_211_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__43));
v___x_212_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_212_, 0, v___x_162_);
lean_ctor_set(v___x_212_, 1, v___x_211_);
v___x_213_ = l_Lean_Syntax_node1(v___x_162_, v___x_210_, v___x_212_);
v___x_214_ = l_Lean_Syntax_node1(v___x_162_, v___x_168_, v___x_213_);
v___x_215_ = lean_obj_once(&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__45, &l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__45_once, _init_l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__45);
v___x_216_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__46));
v___x_217_ = l_Lean_addMacroScope(v_quotContext_158_, v___x_216_, v_currMacroScope_159_);
v___x_218_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_218_, 0, v___x_162_);
lean_ctor_set(v___x_218_, 1, v___x_215_);
lean_ctor_set(v___x_218_, 2, v___x_217_);
lean_ctor_set(v___x_218_, 3, v___x_175_);
v___x_219_ = l_Lean_Syntax_node3(v___x_162_, v___x_201_, v___x_214_, v___x_180_, v___x_218_);
v___x_220_ = lean_obj_once(&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__48, &l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__48_once, _init_l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__48);
v___x_221_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__51));
v___x_222_ = l_Lean_addMacroScope(v_quotContext_158_, v___x_221_, v_currMacroScope_159_);
v___x_223_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__53));
v___x_224_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_224_, 0, v___x_162_);
lean_ctor_set(v___x_224_, 1, v___x_220_);
lean_ctor_set(v___x_224_, 2, v___x_222_);
lean_ctor_set(v___x_224_, 3, v___x_223_);
v___x_225_ = l_Lean_Syntax_node3(v___x_162_, v___x_201_, v___x_180_, v___x_180_, v___x_224_);
v___x_226_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__55));
v___x_227_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__56));
v___x_228_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_228_, 0, v___x_162_);
lean_ctor_set(v___x_228_, 1, v___x_227_);
v___x_229_ = l_Lean_Syntax_node1(v___x_162_, v___x_226_, v___x_228_);
v___x_230_ = lean_obj_once(&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__58, &l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__58_once, _init_l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__58);
v___x_231_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__59));
v___x_232_ = l_Lean_addMacroScope(v_quotContext_158_, v___x_231_, v_currMacroScope_159_);
v___x_233_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_233_, 0, v___x_162_);
lean_ctor_set(v___x_233_, 1, v___x_230_);
lean_ctor_set(v___x_233_, 2, v___x_232_);
lean_ctor_set(v___x_233_, 3, v___x_175_);
v___x_234_ = l_Lean_Syntax_node3(v___x_162_, v___x_201_, v___x_180_, v___x_180_, v___x_233_);
v___x_235_ = lean_obj_once(&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__61, &l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__61_once, _init_l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__61);
v___x_236_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__62));
v___x_237_ = l_Lean_addMacroScope(v_quotContext_158_, v___x_236_, v_currMacroScope_159_);
v___x_238_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_238_, 0, v___x_162_);
lean_ctor_set(v___x_238_, 1, v___x_235_);
lean_ctor_set(v___x_238_, 2, v___x_237_);
lean_ctor_set(v___x_238_, 3, v___x_175_);
v___x_239_ = l_Lean_Syntax_node3(v___x_162_, v___x_201_, v___x_180_, v___x_180_, v___x_238_);
v___x_240_ = lean_unsigned_to_nat(11u);
v___x_241_ = lean_mk_empty_array_with_capacity(v___x_240_);
v___x_242_ = lean_array_push(v___x_241_, v___x_207_);
lean_inc_ref_n(v___x_209_, 4);
v___x_243_ = lean_array_push(v___x_242_, v___x_209_);
v___x_244_ = lean_array_push(v___x_243_, v___x_219_);
v___x_245_ = lean_array_push(v___x_244_, v___x_209_);
v___x_246_ = lean_array_push(v___x_245_, v___x_225_);
v___x_247_ = lean_array_push(v___x_246_, v___x_209_);
v___x_248_ = lean_array_push(v___x_247_, v___x_229_);
v___x_249_ = lean_array_push(v___x_248_, v___x_209_);
v___x_250_ = lean_array_push(v___x_249_, v___x_234_);
v___x_251_ = lean_array_push(v___x_250_, v___x_209_);
v___x_252_ = lean_array_push(v___x_251_, v___x_239_);
v___x_253_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_253_, 0, v___x_162_);
lean_ctor_set(v___x_253_, 1, v___x_168_);
lean_ctor_set(v___x_253_, 2, v___x_252_);
v___x_254_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__63));
v___x_255_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_255_, 0, v___x_162_);
lean_ctor_set(v___x_255_, 1, v___x_254_);
v___x_256_ = l_Lean_Syntax_node3(v___x_162_, v___x_168_, v___x_200_, v___x_253_, v___x_255_);
v___x_257_ = l_Lean_Syntax_node6(v___x_162_, v___x_192_, v___x_193_, v___x_195_, v___x_180_, v___x_198_, v___x_256_, v___x_180_);
v___x_258_ = l_Lean_Syntax_node1(v___x_162_, v___x_168_, v___x_257_);
v___x_259_ = l_Lean_Syntax_node1(v___x_162_, v___x_167_, v___x_258_);
v___x_260_ = l_Lean_Syntax_node1(v___x_162_, v___x_166_, v___x_259_);
v___x_261_ = l_Lean_Syntax_node2(v___x_162_, v___x_188_, v___x_190_, v___x_260_);
v___x_262_ = l_Lean_Syntax_node5(v___x_162_, v___x_168_, v___x_178_, v___x_180_, v___x_187_, v___x_180_, v___x_261_);
v___x_263_ = l_Lean_Syntax_node1(v___x_162_, v___x_167_, v___x_262_);
v___x_264_ = l_Lean_Syntax_node1(v___x_162_, v___x_166_, v___x_263_);
v___x_265_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__64));
v___x_266_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_266_, 0, v___x_162_);
lean_ctor_set(v___x_266_, 1, v___x_265_);
v___x_267_ = l_Lean_Syntax_node3(v___x_162_, v___x_163_, v___x_165_, v___x_264_, v___x_266_);
v___x_268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_268_, 0, v___x_267_);
lean_ctor_set(v___x_268_, 1, v_a_153_);
return v___x_268_;
}
}
}
LEAN_EXPORT lean_object* l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___boxed(lean_object* v_x_269_, lean_object* v_a_270_, lean_object* v_a_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1(v_x_269_, v_a_270_, v_a_271_);
lean_dec_ref(v_a_270_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1(lean_object* v_x_295_, lean_object* v_a_296_, lean_object* v_a_297_){
_start:
{
lean_object* v___x_298_; uint8_t v___x_299_; 
v___x_298_ = ((lean_object*)(l_tacticDeriving__LawfulEq__tactic__step___closed__1));
v___x_299_ = l_Lean_Syntax_isOfKind(v_x_295_, v___x_298_);
if (v___x_299_ == 0)
{
lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_300_ = lean_box(1);
v___x_301_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_301_, 0, v___x_300_);
lean_ctor_set(v___x_301_, 1, v_a_297_);
return v___x_301_;
}
else
{
lean_object* v_ref_302_; uint8_t v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v_ref_302_ = lean_ctor_get(v_a_296_, 5);
v___x_303_ = 0;
v___x_304_ = l_Lean_SourceInfo_fromRef(v_ref_302_, v___x_303_);
v___x_305_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__0));
v___x_306_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__1));
lean_inc_n(v___x_304_, 4);
v___x_307_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_307_, 0, v___x_304_);
lean_ctor_set(v___x_307_, 1, v___x_305_);
v___x_308_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__11));
v___x_309_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__3));
v___x_310_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__4));
v___x_311_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_311_, 0, v___x_304_);
lean_ctor_set(v___x_311_, 1, v___x_310_);
v___x_312_ = l_Lean_Syntax_node1(v___x_304_, v___x_309_, v___x_311_);
v___x_313_ = l_Lean_Syntax_node1(v___x_304_, v___x_308_, v___x_312_);
v___x_314_ = l_Lean_Syntax_node2(v___x_304_, v___x_306_, v___x_307_, v___x_313_);
v___x_315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_315_, 0, v___x_314_);
lean_ctor_set(v___x_315_, 1, v_a_297_);
return v___x_315_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___boxed(lean_object* v_x_316_, lean_object* v_a_317_, lean_object* v_a_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1(v_x_316_, v_a_317_, v_a_318_);
lean_dec_ref(v_a_317_);
return v_res_319_;
}
}
static lean_object* _init_l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__13(void){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_350_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__12));
v___x_351_ = l_String_toRawSubstring_x27(v___x_350_);
return v___x_351_;
}
}
static lean_object* _init_l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__23(void){
_start:
{
lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_375_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__22));
v___x_376_ = l_String_toRawSubstring_x27(v___x_375_);
return v___x_376_;
}
}
static lean_object* _init_l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__34(void){
_start:
{
lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_395_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__33));
v___x_396_ = l_String_toRawSubstring_x27(v___x_395_);
return v___x_396_;
}
}
static lean_object* _init_l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__43(void){
_start:
{
lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_416_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__42));
v___x_417_ = l_String_toRawSubstring_x27(v___x_416_);
return v___x_417_;
}
}
static lean_object* _init_l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__67(void){
_start:
{
lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_462_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__66));
v___x_463_ = l_String_toRawSubstring_x27(v___x_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2(lean_object* v_x_478_, lean_object* v_a_479_, lean_object* v_a_480_){
_start:
{
lean_object* v___x_481_; uint8_t v___x_482_; 
v___x_481_ = ((lean_object*)(l_tacticDeriving__LawfulEq__tactic__step___closed__1));
v___x_482_ = l_Lean_Syntax_isOfKind(v_x_478_, v___x_481_);
if (v___x_482_ == 0)
{
lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_483_ = lean_box(1);
v___x_484_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_484_, 0, v___x_483_);
lean_ctor_set(v___x_484_, 1, v_a_480_);
return v___x_484_;
}
else
{
lean_object* v_quotContext_485_; lean_object* v_currMacroScope_486_; lean_object* v_ref_487_; uint8_t v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v_quotContext_485_ = lean_ctor_get(v_a_479_, 1);
v_currMacroScope_486_ = lean_ctor_get(v_a_479_, 2);
v_ref_487_ = lean_ctor_get(v_a_479_, 5);
v___x_488_ = 0;
v___x_489_ = l_Lean_SourceInfo_fromRef(v_ref_487_, v___x_488_);
v___x_490_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__4));
v___x_491_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__5));
lean_inc_n(v___x_489_, 80);
v___x_492_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_492_, 0, v___x_489_);
lean_ctor_set(v___x_492_, 1, v___x_491_);
v___x_493_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__7));
v___x_494_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__9));
v___x_495_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__11));
v___x_496_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__1));
v___x_497_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__2));
v___x_498_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_498_, 0, v___x_489_);
lean_ctor_set(v___x_498_, 1, v___x_497_);
v___x_499_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__3));
v___x_500_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__4));
v___x_501_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_501_, 0, v___x_489_);
lean_ctor_set(v___x_501_, 1, v___x_499_);
v___x_502_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__7));
v___x_503_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__9));
v___x_504_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__11));
v___x_505_ = lean_obj_once(&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__13, &l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__13_once, _init_l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__13);
v___x_506_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__14));
lean_inc_n(v_currMacroScope_486_, 5);
lean_inc_n(v_quotContext_485_, 5);
v___x_507_ = l_Lean_addMacroScope(v_quotContext_485_, v___x_506_, v_currMacroScope_486_);
v___x_508_ = lean_box(0);
v___x_509_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__16));
v___x_510_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_510_, 0, v___x_489_);
lean_ctor_set(v___x_510_, 1, v___x_505_);
lean_ctor_set(v___x_510_, 2, v___x_507_);
lean_ctor_set(v___x_510_, 3, v___x_509_);
v___x_511_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__17));
v___x_512_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__19));
v___x_513_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__21));
v___x_514_ = lean_obj_once(&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__23, &l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__23_once, _init_l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__23);
v___x_515_ = lean_box(0);
v___x_516_ = l_Lean_addMacroScope(v_quotContext_485_, v___x_515_, v_currMacroScope_486_);
v___x_517_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__25));
v___x_518_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_518_, 0, v___x_489_);
lean_ctor_set(v___x_518_, 1, v___x_514_);
lean_ctor_set(v___x_518_, 2, v___x_516_);
lean_ctor_set(v___x_518_, 3, v___x_517_);
v___x_519_ = l_Lean_Syntax_node1(v___x_489_, v___x_513_, v___x_518_);
lean_inc_ref(v___x_492_);
v___x_520_ = l_Lean_Syntax_node2(v___x_489_, v___x_512_, v___x_492_, v___x_519_);
v___x_521_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__27));
v___x_522_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__29));
v___x_523_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__30));
v___x_524_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_524_, 0, v___x_489_);
lean_ctor_set(v___x_524_, 1, v___x_523_);
lean_inc_ref(v___x_524_);
v___x_525_ = l_Lean_Syntax_node1(v___x_489_, v___x_522_, v___x_524_);
v___x_526_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__31));
v___x_527_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_527_, 0, v___x_489_);
lean_ctor_set(v___x_527_, 1, v___x_526_);
lean_inc_n(v___x_525_, 4);
v___x_528_ = l_Lean_Syntax_node3(v___x_489_, v___x_521_, v___x_525_, v___x_527_, v___x_525_);
v___x_529_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__64));
v___x_530_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_530_, 0, v___x_489_);
lean_ctor_set(v___x_530_, 1, v___x_529_);
lean_inc_ref(v___x_530_);
v___x_531_ = l_Lean_Syntax_node3(v___x_489_, v___x_511_, v___x_520_, v___x_528_, v___x_530_);
v___x_532_ = l_Lean_Syntax_node3(v___x_489_, v___x_495_, v___x_531_, v___x_525_, v___x_525_);
v___x_533_ = l_Lean_Syntax_node2(v___x_489_, v___x_504_, v___x_510_, v___x_532_);
v___x_534_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__32));
v___x_535_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_535_, 0, v___x_489_);
lean_ctor_set(v___x_535_, 1, v___x_534_);
v___x_536_ = lean_obj_once(&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__34, &l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__34_once, _init_l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__34);
v___x_537_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__35));
v___x_538_ = l_Lean_addMacroScope(v_quotContext_485_, v___x_537_, v_currMacroScope_486_);
v___x_539_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__38));
v___x_540_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_540_, 0, v___x_489_);
lean_ctor_set(v___x_540_, 1, v___x_536_);
lean_ctor_set(v___x_540_, 2, v___x_538_);
lean_ctor_set(v___x_540_, 3, v___x_539_);
v___x_541_ = l_Lean_Syntax_node3(v___x_489_, v___x_503_, v___x_533_, v___x_535_, v___x_540_);
v___x_542_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__39));
v___x_543_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_543_, 0, v___x_489_);
lean_ctor_set(v___x_543_, 1, v___x_542_);
v___x_544_ = l_Lean_Syntax_node3(v___x_489_, v___x_502_, v___x_541_, v___x_543_, v___x_525_);
v___x_545_ = lean_obj_once(&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__17, &l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__17_once, _init_l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__17);
v___x_546_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_546_, 0, v___x_489_);
lean_ctor_set(v___x_546_, 1, v___x_495_);
lean_ctor_set(v___x_546_, 2, v___x_545_);
lean_inc_ref_n(v___x_546_, 19);
v___x_547_ = l_Lean_Syntax_node3(v___x_489_, v___x_500_, v___x_501_, v___x_544_, v___x_546_);
v___x_548_ = l_Lean_Syntax_node1(v___x_489_, v___x_495_, v___x_547_);
v___x_549_ = l_Lean_Syntax_node1(v___x_489_, v___x_494_, v___x_548_);
v___x_550_ = l_Lean_Syntax_node1(v___x_489_, v___x_493_, v___x_549_);
v___x_551_ = l_Lean_Syntax_node2(v___x_489_, v___x_496_, v___x_498_, v___x_550_);
v___x_552_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__40));
v___x_553_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__41));
v___x_554_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_554_, 0, v___x_489_);
lean_ctor_set(v___x_554_, 1, v___x_552_);
v___x_555_ = lean_obj_once(&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__43, &l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__43_once, _init_l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__43);
v___x_556_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__45));
v___x_557_ = l_Lean_addMacroScope(v_quotContext_485_, v___x_556_, v_currMacroScope_486_);
v___x_558_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__47));
v___x_559_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_559_, 0, v___x_489_);
lean_ctor_set(v___x_559_, 1, v___x_555_);
lean_ctor_set(v___x_559_, 2, v___x_557_);
lean_ctor_set(v___x_559_, 3, v___x_558_);
v___x_560_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__49));
v___x_561_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__50));
v___x_562_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_562_, 0, v___x_489_);
lean_ctor_set(v___x_562_, 1, v___x_561_);
v___x_563_ = l_Lean_Syntax_node2(v___x_489_, v___x_560_, v___x_562_, v___x_524_);
lean_inc(v___x_563_);
v___x_564_ = l_Lean_Syntax_node2(v___x_489_, v___x_495_, v___x_563_, v___x_563_);
v___x_565_ = l_Lean_Syntax_node2(v___x_489_, v___x_504_, v___x_559_, v___x_564_);
v___x_566_ = l_Lean_Syntax_node2(v___x_489_, v___x_553_, v___x_554_, v___x_565_);
v___x_567_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__52));
v___x_568_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__54));
v___x_569_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__55));
v___x_570_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_570_, 0, v___x_489_);
lean_ctor_set(v___x_570_, 1, v___x_569_);
v___x_571_ = l_Lean_Syntax_node1(v___x_489_, v___x_568_, v___x_570_);
v___x_572_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__57));
v___x_573_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__58));
v___x_574_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_574_, 0, v___x_489_);
lean_ctor_set(v___x_574_, 1, v___x_573_);
v___x_575_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__60));
v___x_576_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__61));
v___x_577_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_577_, 0, v___x_489_);
lean_ctor_set(v___x_577_, 1, v___x_576_);
v___x_578_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__63));
v___x_579_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__64));
v___x_580_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_580_, 0, v___x_489_);
lean_ctor_set(v___x_580_, 1, v___x_579_);
v___x_581_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__28));
v___x_582_ = l_Lean_Syntax_node1(v___x_489_, v___x_581_, v___x_546_);
lean_inc_n(v___x_582_, 2);
v___x_583_ = l_Lean_Syntax_node5(v___x_489_, v___x_578_, v___x_580_, v___x_582_, v___x_546_, v___x_546_, v___x_546_);
v___x_584_ = l_Lean_Syntax_node1(v___x_489_, v___x_495_, v___x_583_);
v___x_585_ = l_Lean_Syntax_node1(v___x_489_, v___x_494_, v___x_584_);
v___x_586_ = l_Lean_Syntax_node1(v___x_489_, v___x_493_, v___x_585_);
lean_inc_ref_n(v___x_577_, 2);
v___x_587_ = l_Lean_Syntax_node2(v___x_489_, v___x_575_, v___x_577_, v___x_586_);
v___x_588_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__25));
v___x_589_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__26));
v___x_590_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_590_, 0, v___x_489_);
lean_ctor_set(v___x_590_, 1, v___x_588_);
v___x_591_ = l_Lean_Syntax_node6(v___x_489_, v___x_589_, v___x_590_, v___x_582_, v___x_546_, v___x_546_, v___x_546_, v___x_546_);
v___x_592_ = l_Lean_Syntax_node1(v___x_489_, v___x_495_, v___x_591_);
v___x_593_ = l_Lean_Syntax_node1(v___x_489_, v___x_494_, v___x_592_);
v___x_594_ = l_Lean_Syntax_node1(v___x_489_, v___x_493_, v___x_593_);
v___x_595_ = l_Lean_Syntax_node2(v___x_489_, v___x_575_, v___x_577_, v___x_594_);
v___x_596_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__0));
v___x_597_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__1));
v___x_598_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_598_, 0, v___x_489_);
lean_ctor_set(v___x_598_, 1, v___x_596_);
v___x_599_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__3));
v___x_600_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__65));
v___x_601_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_601_, 0, v___x_489_);
lean_ctor_set(v___x_601_, 1, v___x_600_);
v___x_602_ = l_Lean_Syntax_node1(v___x_489_, v___x_599_, v___x_601_);
v___x_603_ = l_Lean_Syntax_node1(v___x_489_, v___x_495_, v___x_602_);
v___x_604_ = l_Lean_Syntax_node2(v___x_489_, v___x_597_, v___x_598_, v___x_603_);
v___x_605_ = l_Lean_Syntax_node1(v___x_489_, v___x_495_, v___x_604_);
v___x_606_ = l_Lean_Syntax_node1(v___x_489_, v___x_494_, v___x_605_);
v___x_607_ = l_Lean_Syntax_node1(v___x_489_, v___x_493_, v___x_606_);
v___x_608_ = l_Lean_Syntax_node2(v___x_489_, v___x_575_, v___x_577_, v___x_607_);
v___x_609_ = l_Lean_Syntax_node3(v___x_489_, v___x_495_, v___x_587_, v___x_595_, v___x_608_);
v___x_610_ = l_Lean_Syntax_node2(v___x_489_, v___x_572_, v___x_574_, v___x_609_);
v___x_611_ = l_Lean_Syntax_node1(v___x_489_, v___x_495_, v___x_610_);
v___x_612_ = l_Lean_Syntax_node1(v___x_489_, v___x_494_, v___x_611_);
v___x_613_ = l_Lean_Syntax_node1(v___x_489_, v___x_493_, v___x_612_);
v___x_614_ = l_Lean_Syntax_node2(v___x_489_, v___x_567_, v___x_571_, v___x_613_);
v___x_615_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__12));
v___x_616_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__13));
v___x_617_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_617_, 0, v___x_489_);
lean_ctor_set(v___x_617_, 1, v___x_615_);
v___x_618_ = lean_obj_once(&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__67, &l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__67_once, _init_l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__67);
v___x_619_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__68));
v___x_620_ = l_Lean_addMacroScope(v_quotContext_485_, v___x_619_, v_currMacroScope_486_);
v___x_621_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_621_, 0, v___x_489_);
lean_ctor_set(v___x_621_, 1, v___x_618_);
lean_ctor_set(v___x_621_, 2, v___x_620_);
lean_ctor_set(v___x_621_, 3, v___x_508_);
lean_inc_ref(v___x_621_);
v___x_622_ = l_Lean_Syntax_node1(v___x_489_, v___x_495_, v___x_621_);
v___x_623_ = l_Lean_Syntax_node2(v___x_489_, v___x_616_, v___x_617_, v___x_622_);
v___x_624_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__69));
v___x_625_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__70));
v___x_626_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_626_, 0, v___x_489_);
lean_ctor_set(v___x_626_, 1, v___x_624_);
v___x_627_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__21));
v___x_628_ = l_Lean_Syntax_node2(v___x_489_, v___x_627_, v___x_546_, v___x_621_);
v___x_629_ = l_Lean_Syntax_node1(v___x_489_, v___x_495_, v___x_628_);
v___x_630_ = l_Lean_Syntax_node4(v___x_489_, v___x_625_, v___x_626_, v___x_629_, v___x_546_, v___x_546_);
v___x_631_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__71));
v___x_632_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__72));
v___x_633_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_633_, 0, v___x_489_);
lean_ctor_set(v___x_633_, 1, v___x_631_);
v___x_634_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__29));
v___x_635_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_635_, 0, v___x_489_);
lean_ctor_set(v___x_635_, 1, v___x_634_);
v___x_636_ = l_Lean_Syntax_node1(v___x_489_, v___x_495_, v___x_635_);
v___x_637_ = l_Lean_Syntax_node6(v___x_489_, v___x_632_, v___x_633_, v___x_582_, v___x_546_, v___x_636_, v___x_546_, v___x_546_);
v___x_638_ = lean_unsigned_to_nat(11u);
v___x_639_ = lean_mk_empty_array_with_capacity(v___x_638_);
v___x_640_ = lean_array_push(v___x_639_, v___x_551_);
v___x_641_ = lean_array_push(v___x_640_, v___x_546_);
v___x_642_ = lean_array_push(v___x_641_, v___x_566_);
v___x_643_ = lean_array_push(v___x_642_, v___x_546_);
v___x_644_ = lean_array_push(v___x_643_, v___x_614_);
v___x_645_ = lean_array_push(v___x_644_, v___x_546_);
v___x_646_ = lean_array_push(v___x_645_, v___x_623_);
v___x_647_ = lean_array_push(v___x_646_, v___x_546_);
v___x_648_ = lean_array_push(v___x_647_, v___x_630_);
v___x_649_ = lean_array_push(v___x_648_, v___x_546_);
v___x_650_ = lean_array_push(v___x_649_, v___x_637_);
v___x_651_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_651_, 0, v___x_489_);
lean_ctor_set(v___x_651_, 1, v___x_495_);
lean_ctor_set(v___x_651_, 2, v___x_650_);
v___x_652_ = l_Lean_Syntax_node1(v___x_489_, v___x_494_, v___x_651_);
v___x_653_ = l_Lean_Syntax_node1(v___x_489_, v___x_493_, v___x_652_);
v___x_654_ = l_Lean_Syntax_node3(v___x_489_, v___x_490_, v___x_492_, v___x_653_, v___x_530_);
v___x_655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_655_, 0, v___x_654_);
lean_ctor_set(v___x_655_, 1, v_a_480_);
return v___x_655_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___boxed(lean_object* v_x_656_, lean_object* v_a_657_, lean_object* v_a_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2(v_x_656_, v_a_657_, v_a_658_);
lean_dec_ref(v_a_657_);
return v_res_659_;
}
}
static lean_object* _init_l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__4(void){
_start:
{
lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_670_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__3));
v___x_671_ = l_String_toRawSubstring_x27(v___x_670_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3(lean_object* v_x_688_, lean_object* v_a_689_, lean_object* v_a_690_){
_start:
{
lean_object* v___x_691_; uint8_t v___x_692_; 
v___x_691_ = ((lean_object*)(l_tacticDeriving__LawfulEq__tactic__step___closed__1));
v___x_692_ = l_Lean_Syntax_isOfKind(v_x_688_, v___x_691_);
if (v___x_692_ == 0)
{
lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_693_ = lean_box(1);
v___x_694_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_694_, 0, v___x_693_);
lean_ctor_set(v___x_694_, 1, v_a_690_);
return v___x_694_;
}
else
{
lean_object* v_quotContext_695_; lean_object* v_currMacroScope_696_; lean_object* v_ref_697_; uint8_t v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
v_quotContext_695_ = lean_ctor_get(v_a_689_, 1);
v_currMacroScope_696_ = lean_ctor_get(v_a_689_, 2);
v_ref_697_ = lean_ctor_get(v_a_689_, 5);
v___x_698_ = 0;
v___x_699_ = l_Lean_SourceInfo_fromRef(v_ref_697_, v___x_698_);
v___x_700_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__4));
v___x_701_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__5));
lean_inc_n(v___x_699_, 71);
v___x_702_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_702_, 0, v___x_699_);
lean_ctor_set(v___x_702_, 1, v___x_701_);
v___x_703_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__7));
v___x_704_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__9));
v___x_705_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__11));
v___x_706_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__1));
v___x_707_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__2));
v___x_708_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_708_, 0, v___x_699_);
lean_ctor_set(v___x_708_, 1, v___x_707_);
v___x_709_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__3));
v___x_710_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__4));
v___x_711_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_711_, 0, v___x_699_);
lean_ctor_set(v___x_711_, 1, v___x_709_);
v___x_712_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__7));
v___x_713_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__9));
v___x_714_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__17));
v___x_715_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__19));
v___x_716_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__21));
v___x_717_ = lean_obj_once(&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__23, &l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__23_once, _init_l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__23);
v___x_718_ = lean_box(0);
lean_inc_n(v_currMacroScope_696_, 4);
lean_inc_n(v_quotContext_695_, 4);
v___x_719_ = l_Lean_addMacroScope(v_quotContext_695_, v___x_718_, v_currMacroScope_696_);
v___x_720_ = lean_box(0);
v___x_721_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__0));
v___x_722_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_722_, 0, v___x_699_);
lean_ctor_set(v___x_722_, 1, v___x_717_);
lean_ctor_set(v___x_722_, 2, v___x_719_);
lean_ctor_set(v___x_722_, 3, v___x_721_);
v___x_723_ = l_Lean_Syntax_node1(v___x_699_, v___x_716_, v___x_722_);
lean_inc_ref(v___x_702_);
v___x_724_ = l_Lean_Syntax_node2(v___x_699_, v___x_715_, v___x_702_, v___x_723_);
v___x_725_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__27));
v___x_726_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__29));
v___x_727_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__30));
v___x_728_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_728_, 0, v___x_699_);
lean_ctor_set(v___x_728_, 1, v___x_727_);
lean_inc_ref(v___x_728_);
v___x_729_ = l_Lean_Syntax_node1(v___x_699_, v___x_726_, v___x_728_);
v___x_730_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__31));
v___x_731_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_731_, 0, v___x_699_);
lean_ctor_set(v___x_731_, 1, v___x_730_);
lean_inc_n(v___x_729_, 2);
v___x_732_ = l_Lean_Syntax_node3(v___x_699_, v___x_725_, v___x_729_, v___x_731_, v___x_729_);
v___x_733_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__64));
v___x_734_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_734_, 0, v___x_699_);
lean_ctor_set(v___x_734_, 1, v___x_733_);
lean_inc_ref(v___x_734_);
v___x_735_ = l_Lean_Syntax_node3(v___x_699_, v___x_714_, v___x_724_, v___x_732_, v___x_734_);
v___x_736_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__32));
v___x_737_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_737_, 0, v___x_699_);
lean_ctor_set(v___x_737_, 1, v___x_736_);
v___x_738_ = lean_obj_once(&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__34, &l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__34_once, _init_l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__34);
v___x_739_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__35));
v___x_740_ = l_Lean_addMacroScope(v_quotContext_695_, v___x_739_, v_currMacroScope_696_);
v___x_741_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__2));
v___x_742_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_742_, 0, v___x_699_);
lean_ctor_set(v___x_742_, 1, v___x_738_);
lean_ctor_set(v___x_742_, 2, v___x_740_);
lean_ctor_set(v___x_742_, 3, v___x_741_);
v___x_743_ = l_Lean_Syntax_node3(v___x_699_, v___x_713_, v___x_735_, v___x_737_, v___x_742_);
v___x_744_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__39));
v___x_745_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_745_, 0, v___x_699_);
lean_ctor_set(v___x_745_, 1, v___x_744_);
v___x_746_ = l_Lean_Syntax_node3(v___x_699_, v___x_712_, v___x_743_, v___x_745_, v___x_729_);
v___x_747_ = lean_obj_once(&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__17, &l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__17_once, _init_l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__17);
v___x_748_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_748_, 0, v___x_699_);
lean_ctor_set(v___x_748_, 1, v___x_705_);
lean_ctor_set(v___x_748_, 2, v___x_747_);
lean_inc_ref_n(v___x_748_, 12);
v___x_749_ = l_Lean_Syntax_node3(v___x_699_, v___x_710_, v___x_711_, v___x_746_, v___x_748_);
v___x_750_ = l_Lean_Syntax_node1(v___x_699_, v___x_705_, v___x_749_);
v___x_751_ = l_Lean_Syntax_node1(v___x_699_, v___x_704_, v___x_750_);
v___x_752_ = l_Lean_Syntax_node1(v___x_699_, v___x_703_, v___x_751_);
v___x_753_ = l_Lean_Syntax_node2(v___x_699_, v___x_706_, v___x_708_, v___x_752_);
v___x_754_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__40));
v___x_755_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__41));
v___x_756_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_756_, 0, v___x_699_);
lean_ctor_set(v___x_756_, 1, v___x_754_);
v___x_757_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__11));
v___x_758_ = lean_obj_once(&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__4, &l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__4_once, _init_l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__4);
v___x_759_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__6));
v___x_760_ = l_Lean_addMacroScope(v_quotContext_695_, v___x_759_, v_currMacroScope_696_);
v___x_761_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__8));
v___x_762_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_762_, 0, v___x_699_);
lean_ctor_set(v___x_762_, 1, v___x_758_);
lean_ctor_set(v___x_762_, 2, v___x_760_);
lean_ctor_set(v___x_762_, 3, v___x_761_);
v___x_763_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__49));
v___x_764_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__50));
v___x_765_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_765_, 0, v___x_699_);
lean_ctor_set(v___x_765_, 1, v___x_764_);
v___x_766_ = l_Lean_Syntax_node2(v___x_699_, v___x_763_, v___x_765_, v___x_728_);
lean_inc(v___x_766_);
v___x_767_ = l_Lean_Syntax_node2(v___x_699_, v___x_705_, v___x_766_, v___x_766_);
v___x_768_ = l_Lean_Syntax_node2(v___x_699_, v___x_757_, v___x_762_, v___x_767_);
v___x_769_ = l_Lean_Syntax_node2(v___x_699_, v___x_755_, v___x_756_, v___x_768_);
v___x_770_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__52));
v___x_771_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__54));
v___x_772_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__55));
v___x_773_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_773_, 0, v___x_699_);
lean_ctor_set(v___x_773_, 1, v___x_772_);
v___x_774_ = l_Lean_Syntax_node1(v___x_699_, v___x_771_, v___x_773_);
v___x_775_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__57));
v___x_776_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__58));
v___x_777_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_777_, 0, v___x_699_);
lean_ctor_set(v___x_777_, 1, v___x_776_);
v___x_778_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__60));
v___x_779_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__61));
v___x_780_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_780_, 0, v___x_699_);
lean_ctor_set(v___x_780_, 1, v___x_779_);
v___x_781_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__63));
v___x_782_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__64));
v___x_783_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_783_, 0, v___x_699_);
lean_ctor_set(v___x_783_, 1, v___x_782_);
v___x_784_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__28));
v___x_785_ = l_Lean_Syntax_node1(v___x_699_, v___x_784_, v___x_748_);
lean_inc(v___x_785_);
v___x_786_ = l_Lean_Syntax_node5(v___x_699_, v___x_781_, v___x_783_, v___x_785_, v___x_748_, v___x_748_, v___x_748_);
v___x_787_ = l_Lean_Syntax_node1(v___x_699_, v___x_705_, v___x_786_);
v___x_788_ = l_Lean_Syntax_node1(v___x_699_, v___x_704_, v___x_787_);
v___x_789_ = l_Lean_Syntax_node1(v___x_699_, v___x_703_, v___x_788_);
lean_inc_ref_n(v___x_780_, 2);
v___x_790_ = l_Lean_Syntax_node2(v___x_699_, v___x_778_, v___x_780_, v___x_789_);
v___x_791_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__25));
v___x_792_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__26));
v___x_793_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_793_, 0, v___x_699_);
lean_ctor_set(v___x_793_, 1, v___x_791_);
v___x_794_ = l_Lean_Syntax_node6(v___x_699_, v___x_792_, v___x_793_, v___x_785_, v___x_748_, v___x_748_, v___x_748_, v___x_748_);
v___x_795_ = l_Lean_Syntax_node1(v___x_699_, v___x_705_, v___x_794_);
v___x_796_ = l_Lean_Syntax_node1(v___x_699_, v___x_704_, v___x_795_);
v___x_797_ = l_Lean_Syntax_node1(v___x_699_, v___x_703_, v___x_796_);
v___x_798_ = l_Lean_Syntax_node2(v___x_699_, v___x_778_, v___x_780_, v___x_797_);
v___x_799_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__0));
v___x_800_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__1));
v___x_801_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_801_, 0, v___x_699_);
lean_ctor_set(v___x_801_, 1, v___x_799_);
v___x_802_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__3));
v___x_803_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__65));
v___x_804_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_804_, 0, v___x_699_);
lean_ctor_set(v___x_804_, 1, v___x_803_);
v___x_805_ = l_Lean_Syntax_node1(v___x_699_, v___x_802_, v___x_804_);
v___x_806_ = l_Lean_Syntax_node1(v___x_699_, v___x_705_, v___x_805_);
v___x_807_ = l_Lean_Syntax_node2(v___x_699_, v___x_800_, v___x_801_, v___x_806_);
v___x_808_ = l_Lean_Syntax_node1(v___x_699_, v___x_705_, v___x_807_);
v___x_809_ = l_Lean_Syntax_node1(v___x_699_, v___x_704_, v___x_808_);
v___x_810_ = l_Lean_Syntax_node1(v___x_699_, v___x_703_, v___x_809_);
v___x_811_ = l_Lean_Syntax_node2(v___x_699_, v___x_778_, v___x_780_, v___x_810_);
v___x_812_ = l_Lean_Syntax_node3(v___x_699_, v___x_705_, v___x_790_, v___x_798_, v___x_811_);
v___x_813_ = l_Lean_Syntax_node2(v___x_699_, v___x_775_, v___x_777_, v___x_812_);
v___x_814_ = l_Lean_Syntax_node1(v___x_699_, v___x_705_, v___x_813_);
v___x_815_ = l_Lean_Syntax_node1(v___x_699_, v___x_704_, v___x_814_);
v___x_816_ = l_Lean_Syntax_node1(v___x_699_, v___x_703_, v___x_815_);
v___x_817_ = l_Lean_Syntax_node2(v___x_699_, v___x_770_, v___x_774_, v___x_816_);
v___x_818_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__12));
v___x_819_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__13));
v___x_820_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_820_, 0, v___x_699_);
lean_ctor_set(v___x_820_, 1, v___x_818_);
v___x_821_ = lean_obj_once(&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__67, &l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__67_once, _init_l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__67);
v___x_822_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__68));
v___x_823_ = l_Lean_addMacroScope(v_quotContext_695_, v___x_822_, v_currMacroScope_696_);
v___x_824_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_824_, 0, v___x_699_);
lean_ctor_set(v___x_824_, 1, v___x_821_);
lean_ctor_set(v___x_824_, 2, v___x_823_);
lean_ctor_set(v___x_824_, 3, v___x_720_);
v___x_825_ = l_Lean_Syntax_node1(v___x_699_, v___x_705_, v___x_824_);
lean_inc(v___x_825_);
v___x_826_ = l_Lean_Syntax_node2(v___x_699_, v___x_819_, v___x_820_, v___x_825_);
v___x_827_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__9));
v___x_828_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__10));
v___x_829_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_829_, 0, v___x_699_);
lean_ctor_set(v___x_829_, 1, v___x_827_);
v___x_830_ = l_Lean_Syntax_node2(v___x_699_, v___x_828_, v___x_829_, v___x_825_);
v___x_831_ = lean_unsigned_to_nat(9u);
v___x_832_ = lean_mk_empty_array_with_capacity(v___x_831_);
v___x_833_ = lean_array_push(v___x_832_, v___x_753_);
v___x_834_ = lean_array_push(v___x_833_, v___x_748_);
v___x_835_ = lean_array_push(v___x_834_, v___x_769_);
v___x_836_ = lean_array_push(v___x_835_, v___x_748_);
v___x_837_ = lean_array_push(v___x_836_, v___x_817_);
v___x_838_ = lean_array_push(v___x_837_, v___x_748_);
v___x_839_ = lean_array_push(v___x_838_, v___x_826_);
v___x_840_ = lean_array_push(v___x_839_, v___x_748_);
v___x_841_ = lean_array_push(v___x_840_, v___x_830_);
v___x_842_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_842_, 0, v___x_699_);
lean_ctor_set(v___x_842_, 1, v___x_705_);
lean_ctor_set(v___x_842_, 2, v___x_841_);
v___x_843_ = l_Lean_Syntax_node1(v___x_699_, v___x_704_, v___x_842_);
v___x_844_ = l_Lean_Syntax_node1(v___x_699_, v___x_703_, v___x_843_);
v___x_845_ = l_Lean_Syntax_node3(v___x_699_, v___x_700_, v___x_702_, v___x_844_, v___x_734_);
v___x_846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_846_, 0, v___x_845_);
lean_ctor_set(v___x_846_, 1, v_a_690_);
return v___x_846_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___boxed(lean_object* v_x_847_, lean_object* v_a_848_, lean_object* v_a_849_){
_start:
{
lean_object* v_res_850_; 
v_res_850_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3(v_x_847_, v_a_848_, v_a_849_);
lean_dec_ref(v_a_848_);
return v_res_850_;
}
}
static lean_object* _init_l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__4(void){
_start:
{
lean_object* v___x_856_; lean_object* v___x_857_; 
v___x_856_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__3));
v___x_857_ = l_String_toRawSubstring_x27(v___x_856_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4(lean_object* v_x_868_, lean_object* v_a_869_, lean_object* v_a_870_){
_start:
{
lean_object* v___x_871_; uint8_t v___x_872_; 
v___x_871_ = ((lean_object*)(l_tacticDeriving__LawfulEq__tactic__step___closed__1));
v___x_872_ = l_Lean_Syntax_isOfKind(v_x_868_, v___x_871_);
if (v___x_872_ == 0)
{
lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_873_ = lean_box(1);
v___x_874_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_874_, 0, v___x_873_);
lean_ctor_set(v___x_874_, 1, v_a_870_);
return v___x_874_;
}
else
{
lean_object* v_quotContext_875_; lean_object* v_currMacroScope_876_; lean_object* v_ref_877_; uint8_t v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; 
v_quotContext_875_ = lean_ctor_get(v_a_869_, 1);
v_currMacroScope_876_ = lean_ctor_get(v_a_869_, 2);
v_ref_877_ = lean_ctor_get(v_a_869_, 5);
v___x_878_ = 0;
v___x_879_ = l_Lean_SourceInfo_fromRef(v_ref_877_, v___x_878_);
v___x_880_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__4));
v___x_881_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__5));
lean_inc_n(v___x_879_, 35);
v___x_882_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_882_, 0, v___x_879_);
lean_ctor_set(v___x_882_, 1, v___x_881_);
v___x_883_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__7));
v___x_884_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__9));
v___x_885_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__11));
v___x_886_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__1));
v___x_887_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__2));
v___x_888_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_888_, 0, v___x_879_);
lean_ctor_set(v___x_888_, 1, v___x_887_);
v___x_889_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__3));
v___x_890_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__4));
v___x_891_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_891_, 0, v___x_879_);
lean_ctor_set(v___x_891_, 1, v___x_889_);
v___x_892_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__7));
v___x_893_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__9));
v___x_894_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__17));
v___x_895_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__19));
v___x_896_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__21));
v___x_897_ = lean_obj_once(&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__23, &l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__23_once, _init_l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__23);
v___x_898_ = lean_box(0);
lean_inc_n(v_currMacroScope_876_, 3);
lean_inc_n(v_quotContext_875_, 3);
v___x_899_ = l_Lean_addMacroScope(v_quotContext_875_, v___x_898_, v_currMacroScope_876_);
v___x_900_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__0));
v___x_901_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_901_, 0, v___x_879_);
lean_ctor_set(v___x_901_, 1, v___x_897_);
lean_ctor_set(v___x_901_, 2, v___x_899_);
lean_ctor_set(v___x_901_, 3, v___x_900_);
v___x_902_ = l_Lean_Syntax_node1(v___x_879_, v___x_896_, v___x_901_);
lean_inc_ref(v___x_882_);
v___x_903_ = l_Lean_Syntax_node2(v___x_879_, v___x_895_, v___x_882_, v___x_902_);
v___x_904_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__1));
v___x_905_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__27));
v___x_906_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__29));
v___x_907_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__30));
v___x_908_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_908_, 0, v___x_879_);
lean_ctor_set(v___x_908_, 1, v___x_907_);
lean_inc_ref(v___x_908_);
v___x_909_ = l_Lean_Syntax_node1(v___x_879_, v___x_906_, v___x_908_);
v___x_910_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__31));
v___x_911_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_911_, 0, v___x_879_);
lean_ctor_set(v___x_911_, 1, v___x_910_);
lean_inc_n(v___x_909_, 3);
v___x_912_ = l_Lean_Syntax_node3(v___x_879_, v___x_905_, v___x_909_, v___x_911_, v___x_909_);
v___x_913_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__2));
v___x_914_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_914_, 0, v___x_879_);
lean_ctor_set(v___x_914_, 1, v___x_913_);
v___x_915_ = l_Lean_Syntax_node3(v___x_879_, v___x_904_, v___x_912_, v___x_914_, v___x_909_);
v___x_916_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__64));
v___x_917_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_917_, 0, v___x_879_);
lean_ctor_set(v___x_917_, 1, v___x_916_);
lean_inc_ref(v___x_917_);
v___x_918_ = l_Lean_Syntax_node3(v___x_879_, v___x_894_, v___x_903_, v___x_915_, v___x_917_);
v___x_919_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__32));
v___x_920_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_920_, 0, v___x_879_);
lean_ctor_set(v___x_920_, 1, v___x_919_);
v___x_921_ = lean_obj_once(&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__34, &l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__34_once, _init_l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__34);
v___x_922_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__35));
v___x_923_ = l_Lean_addMacroScope(v_quotContext_875_, v___x_922_, v_currMacroScope_876_);
v___x_924_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__2));
v___x_925_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_925_, 0, v___x_879_);
lean_ctor_set(v___x_925_, 1, v___x_921_);
lean_ctor_set(v___x_925_, 2, v___x_923_);
lean_ctor_set(v___x_925_, 3, v___x_924_);
v___x_926_ = l_Lean_Syntax_node3(v___x_879_, v___x_893_, v___x_918_, v___x_920_, v___x_925_);
v___x_927_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__39));
v___x_928_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_928_, 0, v___x_879_);
lean_ctor_set(v___x_928_, 1, v___x_927_);
v___x_929_ = l_Lean_Syntax_node3(v___x_879_, v___x_892_, v___x_926_, v___x_928_, v___x_909_);
v___x_930_ = lean_obj_once(&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__17, &l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__17_once, _init_l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__17);
v___x_931_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_931_, 0, v___x_879_);
lean_ctor_set(v___x_931_, 1, v___x_885_);
lean_ctor_set(v___x_931_, 2, v___x_930_);
lean_inc_ref(v___x_931_);
v___x_932_ = l_Lean_Syntax_node3(v___x_879_, v___x_890_, v___x_891_, v___x_929_, v___x_931_);
v___x_933_ = l_Lean_Syntax_node1(v___x_879_, v___x_885_, v___x_932_);
v___x_934_ = l_Lean_Syntax_node1(v___x_879_, v___x_884_, v___x_933_);
v___x_935_ = l_Lean_Syntax_node1(v___x_879_, v___x_883_, v___x_934_);
v___x_936_ = l_Lean_Syntax_node2(v___x_879_, v___x_886_, v___x_888_, v___x_935_);
v___x_937_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__40));
v___x_938_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__41));
v___x_939_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_939_, 0, v___x_879_);
lean_ctor_set(v___x_939_, 1, v___x_937_);
v___x_940_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__11));
v___x_941_ = lean_obj_once(&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__4, &l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__4_once, _init_l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__4);
v___x_942_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__6));
v___x_943_ = l_Lean_addMacroScope(v_quotContext_875_, v___x_942_, v_currMacroScope_876_);
v___x_944_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__8));
v___x_945_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_945_, 0, v___x_879_);
lean_ctor_set(v___x_945_, 1, v___x_941_);
lean_ctor_set(v___x_945_, 2, v___x_943_);
lean_ctor_set(v___x_945_, 3, v___x_944_);
v___x_946_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__49));
v___x_947_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__50));
v___x_948_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_948_, 0, v___x_879_);
lean_ctor_set(v___x_948_, 1, v___x_947_);
v___x_949_ = l_Lean_Syntax_node2(v___x_879_, v___x_946_, v___x_948_, v___x_908_);
v___x_950_ = l_Lean_Syntax_node1(v___x_879_, v___x_885_, v___x_949_);
v___x_951_ = l_Lean_Syntax_node2(v___x_879_, v___x_940_, v___x_945_, v___x_950_);
v___x_952_ = l_Lean_Syntax_node2(v___x_879_, v___x_938_, v___x_939_, v___x_951_);
v___x_953_ = l_Lean_Syntax_node3(v___x_879_, v___x_885_, v___x_936_, v___x_931_, v___x_952_);
v___x_954_ = l_Lean_Syntax_node1(v___x_879_, v___x_884_, v___x_953_);
v___x_955_ = l_Lean_Syntax_node1(v___x_879_, v___x_883_, v___x_954_);
v___x_956_ = l_Lean_Syntax_node3(v___x_879_, v___x_880_, v___x_882_, v___x_955_, v___x_917_);
v___x_957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_957_, 0, v___x_956_);
lean_ctor_set(v___x_957_, 1, v_a_870_);
return v___x_957_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___boxed(lean_object* v_x_958_, lean_object* v_a_959_, lean_object* v_a_960_){
_start:
{
lean_object* v_res_961_; 
v_res_961_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4(v_x_958_, v_a_959_, v_a_960_);
lean_dec_ref(v_a_959_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__5(lean_object* v_x_969_, lean_object* v_a_970_, lean_object* v_a_971_){
_start:
{
lean_object* v___x_972_; uint8_t v___x_973_; 
v___x_972_ = ((lean_object*)(l_tacticDeriving__LawfulEq__tactic__step___closed__1));
v___x_973_ = l_Lean_Syntax_isOfKind(v_x_969_, v___x_972_);
if (v___x_973_ == 0)
{
lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_974_ = lean_box(1);
v___x_975_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_975_, 0, v___x_974_);
lean_ctor_set(v___x_975_, 1, v_a_971_);
return v___x_975_;
}
else
{
lean_object* v_ref_976_; uint8_t v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; 
v_ref_976_ = lean_ctor_get(v_a_970_, 5);
v___x_977_ = 0;
v___x_978_ = l_Lean_SourceInfo_fromRef(v_ref_976_, v___x_977_);
v___x_979_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__5___closed__1));
v___x_980_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__5___closed__2));
lean_inc(v___x_978_);
v___x_981_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_981_, 0, v___x_978_);
lean_ctor_set(v___x_981_, 1, v___x_980_);
v___x_982_ = l_Lean_Syntax_node1(v___x_978_, v___x_979_, v___x_981_);
v___x_983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_983_, 0, v___x_982_);
lean_ctor_set(v___x_983_, 1, v_a_971_);
return v___x_983_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__5___boxed(lean_object* v_x_984_, lean_object* v_a_985_, lean_object* v_a_986_){
_start:
{
lean_object* v_res_987_; 
v_res_987_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__5(v_x_984_, v_a_985_, v_a_986_);
lean_dec_ref(v_a_985_);
return v_res_987_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6(lean_object* v_x_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_){
_start:
{
lean_object* v___x_1005_; uint8_t v___x_1006_; 
v___x_1005_ = ((lean_object*)(l_tacticDeriving__LawfulEq__tactic__step___closed__1));
v___x_1006_ = l_Lean_Syntax_isOfKind(v_x_1002_, v___x_1005_);
if (v___x_1006_ == 0)
{
lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1007_ = lean_box(1);
v___x_1008_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1007_);
lean_ctor_set(v___x_1008_, 1, v_a_1004_);
return v___x_1008_;
}
else
{
lean_object* v_ref_1009_; uint8_t v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; 
v_ref_1009_ = lean_ctor_get(v_a_1003_, 5);
v___x_1010_ = 0;
v___x_1011_ = l_Lean_SourceInfo_fromRef(v_ref_1009_, v___x_1010_);
v___x_1012_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__1));
v___x_1013_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__11));
v___x_1014_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__12));
v___x_1015_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__13));
lean_inc_n(v___x_1011_, 9);
v___x_1016_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1011_);
lean_ctor_set(v___x_1016_, 1, v___x_1014_);
v___x_1017_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__29));
v___x_1018_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__30));
v___x_1019_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1011_);
lean_ctor_set(v___x_1019_, 1, v___x_1018_);
v___x_1020_ = l_Lean_Syntax_node1(v___x_1011_, v___x_1017_, v___x_1019_);
v___x_1021_ = l_Lean_Syntax_node1(v___x_1011_, v___x_1013_, v___x_1020_);
v___x_1022_ = l_Lean_Syntax_node2(v___x_1011_, v___x_1015_, v___x_1016_, v___x_1021_);
v___x_1023_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__2));
v___x_1024_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1011_);
lean_ctor_set(v___x_1024_, 1, v___x_1023_);
v___x_1025_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__4));
v___x_1026_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__5));
v___x_1027_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1011_);
lean_ctor_set(v___x_1027_, 1, v___x_1026_);
v___x_1028_ = l_Lean_Syntax_node1(v___x_1011_, v___x_1025_, v___x_1027_);
v___x_1029_ = l_Lean_Syntax_node3(v___x_1011_, v___x_1013_, v___x_1022_, v___x_1024_, v___x_1028_);
v___x_1030_ = l_Lean_Syntax_node1(v___x_1011_, v___x_1012_, v___x_1029_);
v___x_1031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1030_);
lean_ctor_set(v___x_1031_, 1, v_a_1004_);
return v___x_1031_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___boxed(lean_object* v_x_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_){
_start:
{
lean_object* v_res_1035_; 
v_res_1035_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6(v_x_1032_, v_a_1033_, v_a_1034_);
lean_dec_ref(v_a_1033_);
return v_res_1035_;
}
}
static lean_object* _init_l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__1(void){
_start:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1049_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__0));
v___x_1050_ = l_String_toRawSubstring_x27(v___x_1049_);
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1(lean_object* v_x_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_){
_start:
{
lean_object* v___x_1063_; uint8_t v___x_1064_; 
v___x_1063_ = ((lean_object*)(l_tacticDeriving__LawfulEq__tactic___closed__1));
v___x_1064_ = l_Lean_Syntax_isOfKind(v_x_1060_, v___x_1063_);
if (v___x_1064_ == 0)
{
lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1065_ = lean_box(1);
v___x_1066_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1065_);
lean_ctor_set(v___x_1066_, 1, v_a_1062_);
return v___x_1066_;
}
else
{
lean_object* v_quotContext_1067_; lean_object* v_currMacroScope_1068_; lean_object* v_ref_1069_; uint8_t v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; 
v_quotContext_1067_ = lean_ctor_get(v_a_1061_, 1);
v_currMacroScope_1068_ = lean_ctor_get(v_a_1061_, 2);
v_ref_1069_ = lean_ctor_get(v_a_1061_, 5);
v___x_1070_ = 0;
v___x_1071_ = l_Lean_SourceInfo_fromRef(v_ref_1069_, v___x_1070_);
v___x_1072_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__4));
v___x_1073_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__5));
lean_inc_n(v___x_1071_, 51);
v___x_1074_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1071_);
lean_ctor_set(v___x_1074_, 1, v___x_1073_);
v___x_1075_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__7));
v___x_1076_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__9));
v___x_1077_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__11));
v___x_1078_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__12));
v___x_1079_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__13));
v___x_1080_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1071_);
lean_ctor_set(v___x_1080_, 1, v___x_1078_);
v___x_1081_ = lean_obj_once(&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__15, &l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__15_once, _init_l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__15);
v___x_1082_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__16));
lean_inc_n(v_currMacroScope_1068_, 4);
lean_inc_n(v_quotContext_1067_, 4);
v___x_1083_ = l_Lean_addMacroScope(v_quotContext_1067_, v___x_1082_, v_currMacroScope_1068_);
v___x_1084_ = lean_box(0);
v___x_1085_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1071_);
lean_ctor_set(v___x_1085_, 1, v___x_1081_);
lean_ctor_set(v___x_1085_, 2, v___x_1083_);
lean_ctor_set(v___x_1085_, 3, v___x_1084_);
lean_inc_ref(v___x_1085_);
v___x_1086_ = l_Lean_Syntax_node1(v___x_1071_, v___x_1077_, v___x_1085_);
lean_inc_ref(v___x_1080_);
v___x_1087_ = l_Lean_Syntax_node2(v___x_1071_, v___x_1079_, v___x_1080_, v___x_1086_);
v___x_1088_ = lean_obj_once(&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__17, &l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__17_once, _init_l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__17);
v___x_1089_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1071_);
lean_ctor_set(v___x_1089_, 1, v___x_1077_);
lean_ctor_set(v___x_1089_, 2, v___x_1088_);
v___x_1090_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__18));
v___x_1091_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__19));
v___x_1092_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1092_, 0, v___x_1071_);
lean_ctor_set(v___x_1092_, 1, v___x_1090_);
v___x_1093_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__21));
lean_inc_ref_n(v___x_1089_, 18);
v___x_1094_ = l_Lean_Syntax_node2(v___x_1071_, v___x_1093_, v___x_1089_, v___x_1085_);
v___x_1095_ = l_Lean_Syntax_node1(v___x_1071_, v___x_1077_, v___x_1094_);
v___x_1096_ = l_Lean_Syntax_node5(v___x_1071_, v___x_1091_, v___x_1092_, v___x_1095_, v___x_1089_, v___x_1089_, v___x_1089_);
v___x_1097_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__23));
v___x_1098_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__24));
v___x_1099_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1071_);
lean_ctor_set(v___x_1099_, 1, v___x_1098_);
v___x_1100_ = lean_obj_once(&l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__1, &l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__1_once, _init_l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__1);
v___x_1101_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__2));
v___x_1102_ = l_Lean_addMacroScope(v_quotContext_1067_, v___x_1101_, v_currMacroScope_1068_);
v___x_1103_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1103_, 0, v___x_1071_);
lean_ctor_set(v___x_1103_, 1, v___x_1100_);
lean_ctor_set(v___x_1103_, 2, v___x_1102_);
lean_ctor_set(v___x_1103_, 3, v___x_1084_);
lean_inc_ref(v___x_1103_);
v___x_1104_ = l_Lean_Syntax_node1(v___x_1071_, v___x_1077_, v___x_1103_);
v___x_1105_ = l_Lean_Syntax_node2(v___x_1071_, v___x_1079_, v___x_1080_, v___x_1104_);
v___x_1106_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__69));
v___x_1107_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__70));
v___x_1108_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1108_, 0, v___x_1071_);
lean_ctor_set(v___x_1108_, 1, v___x_1106_);
v___x_1109_ = l_Lean_Syntax_node2(v___x_1071_, v___x_1093_, v___x_1089_, v___x_1103_);
v___x_1110_ = l_Lean_Syntax_node1(v___x_1071_, v___x_1077_, v___x_1109_);
v___x_1111_ = l_Lean_Syntax_node4(v___x_1071_, v___x_1107_, v___x_1108_, v___x_1110_, v___x_1089_, v___x_1089_);
v___x_1112_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__25));
v___x_1113_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__26));
v___x_1114_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1071_);
lean_ctor_set(v___x_1114_, 1, v___x_1112_);
v___x_1115_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__28));
v___x_1116_ = l_Lean_Syntax_node1(v___x_1071_, v___x_1115_, v___x_1089_);
v___x_1117_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__29));
v___x_1118_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1071_);
lean_ctor_set(v___x_1118_, 1, v___x_1117_);
v___x_1119_ = l_Lean_Syntax_node1(v___x_1071_, v___x_1077_, v___x_1118_);
v___x_1120_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__30));
v___x_1121_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1121_, 0, v___x_1071_);
lean_ctor_set(v___x_1121_, 1, v___x_1120_);
v___x_1122_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__32));
v___x_1123_ = lean_obj_once(&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__58, &l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__58_once, _init_l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__58);
v___x_1124_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__59));
v___x_1125_ = l_Lean_addMacroScope(v_quotContext_1067_, v___x_1124_, v_currMacroScope_1068_);
v___x_1126_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1126_, 0, v___x_1071_);
lean_ctor_set(v___x_1126_, 1, v___x_1123_);
lean_ctor_set(v___x_1126_, 2, v___x_1125_);
lean_ctor_set(v___x_1126_, 3, v___x_1084_);
v___x_1127_ = l_Lean_Syntax_node3(v___x_1071_, v___x_1122_, v___x_1089_, v___x_1089_, v___x_1126_);
v___x_1128_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__40));
v___x_1129_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1129_, 0, v___x_1071_);
lean_ctor_set(v___x_1129_, 1, v___x_1128_);
v___x_1130_ = lean_obj_once(&l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__61, &l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__61_once, _init_l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__61);
v___x_1131_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__62));
v___x_1132_ = l_Lean_addMacroScope(v_quotContext_1067_, v___x_1131_, v_currMacroScope_1068_);
v___x_1133_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1133_, 0, v___x_1071_);
lean_ctor_set(v___x_1133_, 1, v___x_1130_);
lean_ctor_set(v___x_1133_, 2, v___x_1132_);
lean_ctor_set(v___x_1133_, 3, v___x_1084_);
v___x_1134_ = l_Lean_Syntax_node3(v___x_1071_, v___x_1122_, v___x_1089_, v___x_1089_, v___x_1133_);
v___x_1135_ = l_Lean_Syntax_node3(v___x_1071_, v___x_1077_, v___x_1127_, v___x_1129_, v___x_1134_);
v___x_1136_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__63));
v___x_1137_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1071_);
lean_ctor_set(v___x_1137_, 1, v___x_1136_);
v___x_1138_ = l_Lean_Syntax_node3(v___x_1071_, v___x_1077_, v___x_1121_, v___x_1135_, v___x_1137_);
v___x_1139_ = l_Lean_Syntax_node6(v___x_1071_, v___x_1113_, v___x_1114_, v___x_1116_, v___x_1089_, v___x_1119_, v___x_1138_, v___x_1089_);
v___x_1140_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__4));
v___x_1141_ = ((lean_object*)(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__5));
v___x_1142_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1071_);
lean_ctor_set(v___x_1142_, 1, v___x_1141_);
v___x_1143_ = ((lean_object*)(l_tacticDeriving__LawfulEq__tactic__step___closed__1));
v___x_1144_ = ((lean_object*)(l_tacticDeriving__LawfulEq__tactic__step___closed__2));
v___x_1145_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1145_, 0, v___x_1071_);
lean_ctor_set(v___x_1145_, 1, v___x_1144_);
v___x_1146_ = l_Lean_Syntax_node1(v___x_1071_, v___x_1143_, v___x_1145_);
v___x_1147_ = l_Lean_Syntax_node1(v___x_1071_, v___x_1077_, v___x_1146_);
v___x_1148_ = l_Lean_Syntax_node1(v___x_1071_, v___x_1076_, v___x_1147_);
v___x_1149_ = l_Lean_Syntax_node1(v___x_1071_, v___x_1075_, v___x_1148_);
v___x_1150_ = l_Lean_Syntax_node2(v___x_1071_, v___x_1140_, v___x_1142_, v___x_1149_);
v___x_1151_ = l_Lean_Syntax_node3(v___x_1071_, v___x_1077_, v___x_1139_, v___x_1089_, v___x_1150_);
v___x_1152_ = l_Lean_Syntax_node1(v___x_1071_, v___x_1076_, v___x_1151_);
v___x_1153_ = l_Lean_Syntax_node1(v___x_1071_, v___x_1075_, v___x_1152_);
lean_inc_ref(v___x_1099_);
v___x_1154_ = l_Lean_Syntax_node2(v___x_1071_, v___x_1097_, v___x_1099_, v___x_1153_);
v___x_1155_ = l_Lean_Syntax_node5(v___x_1071_, v___x_1077_, v___x_1105_, v___x_1089_, v___x_1111_, v___x_1089_, v___x_1154_);
v___x_1156_ = l_Lean_Syntax_node1(v___x_1071_, v___x_1076_, v___x_1155_);
v___x_1157_ = l_Lean_Syntax_node1(v___x_1071_, v___x_1075_, v___x_1156_);
v___x_1158_ = l_Lean_Syntax_node2(v___x_1071_, v___x_1097_, v___x_1099_, v___x_1157_);
v___x_1159_ = l_Lean_Syntax_node5(v___x_1071_, v___x_1077_, v___x_1087_, v___x_1089_, v___x_1096_, v___x_1089_, v___x_1158_);
v___x_1160_ = l_Lean_Syntax_node1(v___x_1071_, v___x_1076_, v___x_1159_);
v___x_1161_ = l_Lean_Syntax_node1(v___x_1071_, v___x_1075_, v___x_1160_);
v___x_1162_ = ((lean_object*)(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__64));
v___x_1163_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1163_, 0, v___x_1071_);
lean_ctor_set(v___x_1163_, 1, v___x_1162_);
v___x_1164_ = l_Lean_Syntax_node3(v___x_1071_, v___x_1072_, v___x_1074_, v___x_1161_, v___x_1163_);
v___x_1165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1165_, 0, v___x_1164_);
lean_ctor_set(v___x_1165_, 1, v_a_1062_);
return v___x_1165_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___boxed(lean_object* v_x_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_){
_start:
{
lean_object* v_res_1169_; 
v_res_1169_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1(v_x_1166_, v_a_1167_, v_a_1168_);
lean_dec_ref(v_a_1167_);
return v_res_1169_;
}
}
lean_object* runtime_initialize_Init_Core(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Bool(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Classical(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_LawfulBEqTactics(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Core(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Classical(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_LawfulBEqTactics(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Core(uint8_t builtin);
lean_object* initialize_Init_Data_Bool(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Classical(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_LawfulBEqTactics(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Core(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Classical(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_LawfulBEqTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_LawfulBEqTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_LawfulBEqTactics(builtin);
}
#ifdef __cplusplus
}
#endif

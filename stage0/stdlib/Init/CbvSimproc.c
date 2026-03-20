// Lean compiler output
// Module: Init.CbvSimproc
// Imports: public meta import Init.Data.ToString.Name public import Init.Tactics import Init.Meta.Defs
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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_simpPost;
extern lean_object* l_Lean_Parser_Tactic_simpPre;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_syntax_ident(lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_cbvSimprocEval___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "cbvSimprocEval"};
static const lean_object* l_Lean_Parser_cbvSimprocEval___closed__0 = (const lean_object*)&l_Lean_Parser_cbvSimprocEval___closed__0_value;
static const lean_string_object l_Lean_Parser_cbvSimprocEval___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Parser_cbvSimprocEval___closed__1 = (const lean_object*)&l_Lean_Parser_cbvSimprocEval___closed__1_value;
static const lean_string_object l_Lean_Parser_cbvSimprocEval___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Parser_cbvSimprocEval___closed__2 = (const lean_object*)&l_Lean_Parser_cbvSimprocEval___closed__2_value;
static const lean_ctor_object l_Lean_Parser_cbvSimprocEval___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_cbvSimprocEval___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_cbvSimprocEval___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_cbvSimprocEval___closed__3_value_aux_0),((lean_object*)&l_Lean_Parser_cbvSimprocEval___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_cbvSimprocEval___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_cbvSimprocEval___closed__3_value_aux_1),((lean_object*)&l_Lean_Parser_cbvSimprocEval___closed__0_value),LEAN_SCALAR_PTR_LITERAL(246, 221, 189, 14, 79, 87, 225, 132)}};
static const lean_object* l_Lean_Parser_cbvSimprocEval___closed__3 = (const lean_object*)&l_Lean_Parser_cbvSimprocEval___closed__3_value;
static const lean_string_object l_Lean_Parser_cbvSimprocEval___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "cbv_eval"};
static const lean_object* l_Lean_Parser_cbvSimprocEval___closed__4 = (const lean_object*)&l_Lean_Parser_cbvSimprocEval___closed__4_value;
static const lean_ctor_object l_Lean_Parser_cbvSimprocEval___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_cbvSimprocEval___closed__4_value)}};
static const lean_object* l_Lean_Parser_cbvSimprocEval___closed__5 = (const lean_object*)&l_Lean_Parser_cbvSimprocEval___closed__5_value;
static const lean_ctor_object l_Lean_Parser_cbvSimprocEval___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lean_Parser_cbvSimprocEval___closed__0_value),((lean_object*)&l_Lean_Parser_cbvSimprocEval___closed__3_value),((lean_object*)&l_Lean_Parser_cbvSimprocEval___closed__5_value)}};
static const lean_object* l_Lean_Parser_cbvSimprocEval___closed__6 = (const lean_object*)&l_Lean_Parser_cbvSimprocEval___closed__6_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_cbvSimprocEval = (const lean_object*)&l_Lean_Parser_cbvSimprocEval___closed__6_value;
static const lean_string_object l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "command__Cbv_simproc____(_):=_"};
static const lean_object* l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__0 = (const lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__0_value;
static const lean_ctor_object l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_cbvSimprocEval___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_cbvSimprocEval___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(12, 189, 177, 127, 220, 246, 55, 104)}};
static const lean_object* l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__1 = (const lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__1_value;
static const lean_string_object l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__2 = (const lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__2_value;
static const lean_ctor_object l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3 = (const lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value;
static const lean_string_object l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "optional"};
static const lean_object* l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__4 = (const lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__4_value;
static const lean_ctor_object l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__4_value),LEAN_SCALAR_PTR_LITERAL(233, 141, 154, 50, 143, 135, 42, 252)}};
static const lean_object* l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__5 = (const lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__5_value;
static const lean_string_object l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "docComment"};
static const lean_object* l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__6 = (const lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__6_value;
static const lean_ctor_object l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__6_value),LEAN_SCALAR_PTR_LITERAL(229, 56, 215, 222, 243, 187, 251, 54)}};
static const lean_object* l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__7 = (const lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__7_value;
static const lean_ctor_object l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__7_value)}};
static const lean_object* l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__8 = (const lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__8_value;
static const lean_ctor_object l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__5_value),((lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__8_value)}};
static const lean_object* l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__9 = (const lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__9_value;
static const lean_string_object l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__10 = (const lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__10_value;
static const lean_ctor_object l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__10_value),LEAN_SCALAR_PTR_LITERAL(144, 113, 220, 36, 163, 13, 57, 223)}};
static const lean_object* l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__11 = (const lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__11_value;
static const lean_ctor_object l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__11_value)}};
static const lean_object* l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__12 = (const lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__12_value;
static const lean_ctor_object l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value),((lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__9_value),((lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__12_value)}};
static const lean_object* l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__13 = (const lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__13_value;
static const lean_string_object l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "cbv_simproc "};
static const lean_object* l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__14 = (const lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__14_value;
static const lean_ctor_object l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__14_value)}};
static const lean_object* l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__15 = (const lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__15_value;
static const lean_ctor_object l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value),((lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__13_value),((lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__15_value)}};
static const lean_object* l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__16 = (const lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__16_value;
static const lean_string_object l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "orelse"};
static const lean_object* l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__17 = (const lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__17_value;
static const lean_ctor_object l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__17_value),LEAN_SCALAR_PTR_LITERAL(78, 76, 4, 51, 251, 212, 116, 5)}};
static const lean_object* l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__18 = (const lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__18_value;
static lean_once_cell_t l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__19;
static lean_once_cell_t l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__20;
static lean_once_cell_t l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__21;
static lean_once_cell_t l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__22;
static const lean_string_object l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__23 = (const lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__23_value;
static const lean_ctor_object l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__23_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__24 = (const lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__24_value;
static const lean_ctor_object l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__24_value)}};
static const lean_object* l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__25 = (const lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__25_value;
static lean_once_cell_t l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__26;
static const lean_string_object l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " ("};
static const lean_object* l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__27 = (const lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__27_value;
static const lean_ctor_object l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__27_value)}};
static const lean_object* l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__28 = (const lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__28_value;
static lean_once_cell_t l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__29;
static const lean_string_object l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__30 = (const lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__30_value;
static const lean_ctor_object l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__30_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__31 = (const lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__31_value;
static const lean_ctor_object l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__31_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__32 = (const lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__32_value;
static lean_once_cell_t l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__33;
static const lean_string_object l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__34 = (const lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__34_value;
static const lean_ctor_object l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__34_value)}};
static const lean_object* l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__35 = (const lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__35_value;
static lean_once_cell_t l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__36;
static const lean_string_object l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__37 = (const lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__37_value;
static const lean_ctor_object l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__37_value)}};
static const lean_object* l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__38 = (const lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__38_value;
static lean_once_cell_t l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__39;
static lean_once_cell_t l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__40;
static lean_once_cell_t l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__41;
LEAN_EXPORT lean_object* l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d__;
static const lean_string_object l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "command_Cbv_simproc_decl_(_):=_"};
static const lean_object* l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__0 = (const lean_object*)&l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__0_value;
static const lean_ctor_object l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_cbvSimprocEval___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_cbvSimprocEval___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 241, 23, 23, 219, 215, 248, 52)}};
static const lean_object* l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__1 = (const lean_object*)&l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__1_value;
static const lean_string_object l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "cbv_simproc_decl "};
static const lean_object* l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__2 = (const lean_object*)&l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__2_value;
static const lean_ctor_object l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__2_value)}};
static const lean_object* l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__3 = (const lean_object*)&l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__3_value;
static const lean_ctor_object l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value),((lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__9_value),((lean_object*)&l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__3_value)}};
static const lean_object* l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__4 = (const lean_object*)&l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__4_value;
static const lean_ctor_object l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value),((lean_object*)&l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__4_value),((lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__25_value)}};
static const lean_object* l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__5 = (const lean_object*)&l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__5_value;
static const lean_ctor_object l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value),((lean_object*)&l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__5_value),((lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__28_value)}};
static const lean_object* l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__6 = (const lean_object*)&l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__6_value;
static const lean_ctor_object l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value),((lean_object*)&l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__6_value),((lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__32_value)}};
static const lean_object* l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__7 = (const lean_object*)&l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__7_value;
static const lean_ctor_object l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value),((lean_object*)&l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__7_value),((lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__35_value)}};
static const lean_object* l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__8 = (const lean_object*)&l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__8_value;
static const lean_ctor_object l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value),((lean_object*)&l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__8_value),((lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__38_value)}};
static const lean_object* l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__9 = (const lean_object*)&l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__9_value;
static const lean_ctor_object l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value),((lean_object*)&l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__9_value),((lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__32_value)}};
static const lean_object* l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__10 = (const lean_object*)&l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__10_value;
static const lean_ctor_object l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__10_value)}};
static const lean_object* l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__11 = (const lean_object*)&l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__11_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d__ = (const lean_object*)&l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__11_value;
static const lean_string_object l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "command__Builtin_cbv_simproc____(_):=_"};
static const lean_object* l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__0 = (const lean_object*)&l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__0_value;
static const lean_ctor_object l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_cbvSimprocEval___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_cbvSimprocEval___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(232, 62, 116, 147, 179, 57, 251, 139)}};
static const lean_object* l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__1 = (const lean_object*)&l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__1_value;
static const lean_string_object l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "builtin_cbv_simproc "};
static const lean_object* l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__2 = (const lean_object*)&l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__2_value;
static const lean_ctor_object l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__2_value)}};
static const lean_object* l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__3 = (const lean_object*)&l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value;
static const lean_ctor_object l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value),((lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__13_value),((lean_object*)&l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value)}};
static const lean_object* l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__4 = (const lean_object*)&l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__4_value;
static lean_once_cell_t l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__5;
static lean_once_cell_t l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__6;
static lean_once_cell_t l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__7;
static lean_once_cell_t l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__8;
static lean_once_cell_t l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__9;
static lean_once_cell_t l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__10;
static lean_once_cell_t l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__11;
static lean_once_cell_t l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__12;
LEAN_EXPORT lean_object* l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d__;
static const lean_string_object l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "command_Builtin_cbv_simproc_decl_(_):=_"};
static const lean_object* l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__0 = (const lean_object*)&l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__0_value;
static const lean_ctor_object l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_cbvSimprocEval___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_cbvSimprocEval___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(221, 202, 177, 39, 69, 237, 175, 236)}};
static const lean_object* l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__1 = (const lean_object*)&l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__1_value;
static const lean_string_object l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "builtin_cbv_simproc_decl "};
static const lean_object* l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__2 = (const lean_object*)&l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__2_value;
static const lean_ctor_object l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__2_value)}};
static const lean_object* l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__3 = (const lean_object*)&l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__3_value;
static const lean_ctor_object l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value),((lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__9_value),((lean_object*)&l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__3_value)}};
static const lean_object* l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__4 = (const lean_object*)&l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__4_value;
static const lean_ctor_object l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value),((lean_object*)&l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__4_value),((lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__25_value)}};
static const lean_object* l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__5 = (const lean_object*)&l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__5_value;
static const lean_ctor_object l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value),((lean_object*)&l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__5_value),((lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__28_value)}};
static const lean_object* l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__6 = (const lean_object*)&l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__6_value;
static const lean_ctor_object l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value),((lean_object*)&l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__6_value),((lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__32_value)}};
static const lean_object* l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__7 = (const lean_object*)&l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__7_value;
static const lean_ctor_object l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value),((lean_object*)&l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__7_value),((lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__35_value)}};
static const lean_object* l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__8 = (const lean_object*)&l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__8_value;
static const lean_ctor_object l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value),((lean_object*)&l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__8_value),((lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__38_value)}};
static const lean_object* l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__9 = (const lean_object*)&l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__9_value;
static const lean_ctor_object l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value),((lean_object*)&l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__9_value),((lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__32_value)}};
static const lean_object* l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__10 = (const lean_object*)&l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__10_value;
static const lean_ctor_object l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__10_value)}};
static const lean_object* l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__11 = (const lean_object*)&l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__11_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d__ = (const lean_object*)&l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__11_value;
static const lean_string_object l_Lean_Parser_cbvSimprocPattern___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "cbvSimprocPattern"};
static const lean_object* l_Lean_Parser_cbvSimprocPattern___closed__0 = (const lean_object*)&l_Lean_Parser_cbvSimprocPattern___closed__0_value;
static const lean_ctor_object l_Lean_Parser_cbvSimprocPattern___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_cbvSimprocEval___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_cbvSimprocPattern___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_cbvSimprocPattern___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_cbvSimprocEval___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_cbvSimprocPattern___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_cbvSimprocPattern___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_cbvSimprocPattern___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 75, 142, 45, 135, 67, 101, 69)}};
static const lean_object* l_Lean_Parser_cbvSimprocPattern___closed__1 = (const lean_object*)&l_Lean_Parser_cbvSimprocPattern___closed__1_value;
static const lean_string_object l_Lean_Parser_cbvSimprocPattern___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "cbv_simproc_pattern% "};
static const lean_object* l_Lean_Parser_cbvSimprocPattern___closed__2 = (const lean_object*)&l_Lean_Parser_cbvSimprocPattern___closed__2_value;
static const lean_ctor_object l_Lean_Parser_cbvSimprocPattern___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_cbvSimprocPattern___closed__2_value)}};
static const lean_object* l_Lean_Parser_cbvSimprocPattern___closed__3 = (const lean_object*)&l_Lean_Parser_cbvSimprocPattern___closed__3_value;
static const lean_ctor_object l_Lean_Parser_cbvSimprocPattern___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value),((lean_object*)&l_Lean_Parser_cbvSimprocPattern___closed__3_value),((lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__32_value)}};
static const lean_object* l_Lean_Parser_cbvSimprocPattern___closed__4 = (const lean_object*)&l_Lean_Parser_cbvSimprocPattern___closed__4_value;
static const lean_string_object l_Lean_Parser_cbvSimprocPattern___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " => "};
static const lean_object* l_Lean_Parser_cbvSimprocPattern___closed__5 = (const lean_object*)&l_Lean_Parser_cbvSimprocPattern___closed__5_value;
static const lean_ctor_object l_Lean_Parser_cbvSimprocPattern___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_cbvSimprocPattern___closed__5_value)}};
static const lean_object* l_Lean_Parser_cbvSimprocPattern___closed__6 = (const lean_object*)&l_Lean_Parser_cbvSimprocPattern___closed__6_value;
static const lean_ctor_object l_Lean_Parser_cbvSimprocPattern___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value),((lean_object*)&l_Lean_Parser_cbvSimprocPattern___closed__4_value),((lean_object*)&l_Lean_Parser_cbvSimprocPattern___closed__6_value)}};
static const lean_object* l_Lean_Parser_cbvSimprocPattern___closed__7 = (const lean_object*)&l_Lean_Parser_cbvSimprocPattern___closed__7_value;
static const lean_ctor_object l_Lean_Parser_cbvSimprocPattern___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value),((lean_object*)&l_Lean_Parser_cbvSimprocPattern___closed__7_value),((lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__25_value)}};
static const lean_object* l_Lean_Parser_cbvSimprocPattern___closed__8 = (const lean_object*)&l_Lean_Parser_cbvSimprocPattern___closed__8_value;
static const lean_ctor_object l_Lean_Parser_cbvSimprocPattern___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_cbvSimprocPattern___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_cbvSimprocPattern___closed__8_value)}};
static const lean_object* l_Lean_Parser_cbvSimprocPattern___closed__9 = (const lean_object*)&l_Lean_Parser_cbvSimprocPattern___closed__9_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_cbvSimprocPattern = (const lean_object*)&l_Lean_Parser_cbvSimprocPattern___closed__9_value;
static const lean_string_object l_Lean_Parser_cbvSimprocPatternBuiltin___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "cbvSimprocPatternBuiltin"};
static const lean_object* l_Lean_Parser_cbvSimprocPatternBuiltin___closed__0 = (const lean_object*)&l_Lean_Parser_cbvSimprocPatternBuiltin___closed__0_value;
static const lean_ctor_object l_Lean_Parser_cbvSimprocPatternBuiltin___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_cbvSimprocEval___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_cbvSimprocPatternBuiltin___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_cbvSimprocPatternBuiltin___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_cbvSimprocEval___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_cbvSimprocPatternBuiltin___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_cbvSimprocPatternBuiltin___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_cbvSimprocPatternBuiltin___closed__0_value),LEAN_SCALAR_PTR_LITERAL(43, 134, 28, 30, 122, 199, 7, 31)}};
static const lean_object* l_Lean_Parser_cbvSimprocPatternBuiltin___closed__1 = (const lean_object*)&l_Lean_Parser_cbvSimprocPatternBuiltin___closed__1_value;
static const lean_string_object l_Lean_Parser_cbvSimprocPatternBuiltin___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "builtin_cbv_simproc_pattern% "};
static const lean_object* l_Lean_Parser_cbvSimprocPatternBuiltin___closed__2 = (const lean_object*)&l_Lean_Parser_cbvSimprocPatternBuiltin___closed__2_value;
static const lean_ctor_object l_Lean_Parser_cbvSimprocPatternBuiltin___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_cbvSimprocPatternBuiltin___closed__2_value)}};
static const lean_object* l_Lean_Parser_cbvSimprocPatternBuiltin___closed__3 = (const lean_object*)&l_Lean_Parser_cbvSimprocPatternBuiltin___closed__3_value;
static const lean_ctor_object l_Lean_Parser_cbvSimprocPatternBuiltin___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value),((lean_object*)&l_Lean_Parser_cbvSimprocPatternBuiltin___closed__3_value),((lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__32_value)}};
static const lean_object* l_Lean_Parser_cbvSimprocPatternBuiltin___closed__4 = (const lean_object*)&l_Lean_Parser_cbvSimprocPatternBuiltin___closed__4_value;
static const lean_ctor_object l_Lean_Parser_cbvSimprocPatternBuiltin___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value),((lean_object*)&l_Lean_Parser_cbvSimprocPatternBuiltin___closed__4_value),((lean_object*)&l_Lean_Parser_cbvSimprocPattern___closed__6_value)}};
static const lean_object* l_Lean_Parser_cbvSimprocPatternBuiltin___closed__5 = (const lean_object*)&l_Lean_Parser_cbvSimprocPatternBuiltin___closed__5_value;
static const lean_ctor_object l_Lean_Parser_cbvSimprocPatternBuiltin___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value),((lean_object*)&l_Lean_Parser_cbvSimprocPatternBuiltin___closed__5_value),((lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__25_value)}};
static const lean_object* l_Lean_Parser_cbvSimprocPatternBuiltin___closed__6 = (const lean_object*)&l_Lean_Parser_cbvSimprocPatternBuiltin___closed__6_value;
static const lean_ctor_object l_Lean_Parser_cbvSimprocPatternBuiltin___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_cbvSimprocPatternBuiltin___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_cbvSimprocPatternBuiltin___closed__6_value)}};
static const lean_object* l_Lean_Parser_cbvSimprocPatternBuiltin___closed__7 = (const lean_object*)&l_Lean_Parser_cbvSimprocPatternBuiltin___closed__7_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_cbvSimprocPatternBuiltin = (const lean_object*)&l_Lean_Parser_cbvSimprocPatternBuiltin___closed__7_value;
static const lean_string_object l_Lean_Parser_Attr_cbvSimprocAttr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l_Lean_Parser_Attr_cbvSimprocAttr___closed__0 = (const lean_object*)&l_Lean_Parser_Attr_cbvSimprocAttr___closed__0_value;
static const lean_string_object l_Lean_Parser_Attr_cbvSimprocAttr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "cbvSimprocAttr"};
static const lean_object* l_Lean_Parser_Attr_cbvSimprocAttr___closed__1 = (const lean_object*)&l_Lean_Parser_Attr_cbvSimprocAttr___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Attr_cbvSimprocAttr___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_cbvSimprocEval___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Attr_cbvSimprocAttr___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_cbvSimprocAttr___closed__2_value_aux_0),((lean_object*)&l_Lean_Parser_cbvSimprocEval___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Attr_cbvSimprocAttr___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_cbvSimprocAttr___closed__2_value_aux_1),((lean_object*)&l_Lean_Parser_Attr_cbvSimprocAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Parser_Attr_cbvSimprocAttr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_cbvSimprocAttr___closed__2_value_aux_2),((lean_object*)&l_Lean_Parser_Attr_cbvSimprocAttr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(87, 243, 70, 210, 214, 166, 207, 129)}};
static const lean_object* l_Lean_Parser_Attr_cbvSimprocAttr___closed__2 = (const lean_object*)&l_Lean_Parser_Attr_cbvSimprocAttr___closed__2_value;
static const lean_string_object l_Lean_Parser_Attr_cbvSimprocAttr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "cbv_simproc"};
static const lean_object* l_Lean_Parser_Attr_cbvSimprocAttr___closed__3 = (const lean_object*)&l_Lean_Parser_Attr_cbvSimprocAttr___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Attr_cbvSimprocAttr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_cbvSimprocAttr___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Attr_cbvSimprocAttr___closed__4 = (const lean_object*)&l_Lean_Parser_Attr_cbvSimprocAttr___closed__4_value;
static lean_once_cell_t l_Lean_Parser_Attr_cbvSimprocAttr___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_cbvSimprocAttr___closed__5;
static lean_once_cell_t l_Lean_Parser_Attr_cbvSimprocAttr___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_cbvSimprocAttr___closed__6;
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_cbvSimprocAttr;
static const lean_string_object l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "cbvSimprocBuiltinAttr"};
static const lean_object* l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__0 = (const lean_object*)&l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_cbvSimprocEval___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_cbvSimprocEval___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Attr_cbvSimprocAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(179, 203, 241, 108, 113, 206, 69, 37)}};
static const lean_object* l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__1 = (const lean_object*)&l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__1_value;
static const lean_string_object l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "builtin_cbv_simproc"};
static const lean_object* l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__2 = (const lean_object*)&l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__3 = (const lean_object*)&l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__4;
static lean_once_cell_t l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__5;
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_cbvSimprocBuiltinAttr;
static const lean_string_object l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__0 = (const lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__0_value;
static const lean_string_object l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__1 = (const lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__1_value;
static const lean_string_object l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "def"};
static const lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__2 = (const lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__2_value;
static const lean_string_object l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "declId"};
static const lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__3 = (const lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__3_value;
static const lean_string_object l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "optDeclSig"};
static const lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__4 = (const lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__4_value;
static const lean_string_object l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__5 = (const lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__5_value;
static const lean_string_object l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__6 = (const lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__6_value;
static const lean_ctor_object l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_cbvSimprocEval___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__7_value_aux_0),((lean_object*)&l_Lean_Parser_cbvSimprocEval___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__7_value_aux_1),((lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__7_value_aux_2),((lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(77, 126, 241, 117, 174, 189, 108, 62)}};
static const lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__7 = (const lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__7_value;
static const lean_string_object l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__8 = (const lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__8_value;
static const lean_string_object l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declValSimple"};
static const lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__9 = (const lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__9_value;
static const lean_string_object l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__10 = (const lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__10_value;
static const lean_string_object l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Termination"};
static const lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__11 = (const lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__11_value;
static const lean_string_object l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "suffix"};
static const lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__12 = (const lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__12_value;
static const lean_ctor_object l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_cbvSimprocEval___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__13_value_aux_0),((lean_object*)&l_Lean_Parser_cbvSimprocEval___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__13_value_aux_1),((lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__11_value),LEAN_SCALAR_PTR_LITERAL(128, 225, 226, 49, 186, 161, 212, 105)}};
static const lean_ctor_object l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__13_value_aux_2),((lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(245, 187, 99, 45, 217, 244, 244, 120)}};
static const lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__13 = (const lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__13_value;
static const lean_string_object l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "cbv_simproc_pattern%"};
static const lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__14 = (const lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__14_value;
static const lean_string_object l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__15 = (const lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__15_value;
static const lean_string_object l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__16 = (const lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__16_value;
static const lean_string_object l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Sym"};
static const lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__17 = (const lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__17_value;
static const lean_string_object l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Simp"};
static const lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__18 = (const lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__18_value;
static const lean_string_object l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Simproc"};
static const lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__19 = (const lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__19_value;
static const lean_ctor_object l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_cbvSimprocEval___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__20_value_aux_0),((lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__20_value_aux_1),((lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__17_value),LEAN_SCALAR_PTR_LITERAL(243, 157, 148, 19, 62, 70, 252, 55)}};
static const lean_ctor_object l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__20_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__20_value_aux_2),((lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(27, 118, 156, 162, 140, 167, 154, 191)}};
static const lean_ctor_object l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__20_value_aux_3),((lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(243, 37, 220, 98, 36, 118, 162, 63)}};
static const lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__20 = (const lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__20_value;
static const lean_string_object l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__21 = (const lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__21_value;
static const lean_ctor_object l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__22 = (const lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__22_value;
static const lean_string_object l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__23 = (const lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__23_value;
static const lean_string_object l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "declaration"};
static const lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__24 = (const lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__24_value;
static const lean_ctor_object l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_cbvSimprocEval___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__25_value_aux_0),((lean_object*)&l_Lean_Parser_cbvSimprocEval___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__25_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__25_value_aux_1),((lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__23_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__25_value_aux_2),((lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__24_value),LEAN_SCALAR_PTR_LITERAL(157, 246, 223, 221, 242, 35, 238, 117)}};
static const lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__25 = (const lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__25_value;
static const lean_string_object l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declModifiers"};
static const lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__26 = (const lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__26_value;
static const lean_ctor_object l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_cbvSimprocEval___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__27_value_aux_0),((lean_object*)&l_Lean_Parser_cbvSimprocEval___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__27_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__27_value_aux_1),((lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__23_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__27_value_aux_2),((lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__26_value),LEAN_SCALAR_PTR_LITERAL(0, 165, 146, 53, 36, 89, 7, 202)}};
static const lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__27 = (const lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__27_value;
static lean_once_cell_t l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__28;
static const lean_array_object l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__29 = (const lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__29_value;
static const lean_ctor_object l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_cbvSimprocEval___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__30_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__30_value_aux_0),((lean_object*)&l_Lean_Parser_cbvSimprocEval___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__30_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__30_value_aux_1),((lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__23_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__30_value_aux_2),((lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__6_value),LEAN_SCALAR_PTR_LITERAL(44, 76, 179, 33, 27, 4, 201, 125)}};
static const lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__30 = (const lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__30_value;
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "builtin_cbv_simproc_pattern%"};
static const lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__0 = (const lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d____1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__0 = (const lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__0_value;
static const lean_string_object l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "cbv_simproc_decl"};
static const lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__1 = (const lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__1_value;
static const lean_string_object l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__2 = (const lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__2_value;
static const lean_string_object l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "attribute"};
static const lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__3 = (const lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__3_value;
static const lean_ctor_object l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_cbvSimprocEval___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__4_value_aux_0),((lean_object*)&l_Lean_Parser_cbvSimprocEval___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__4_value_aux_1),((lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__23_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__4_value_aux_2),((lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(79, 30, 18, 84, 71, 173, 185, 159)}};
static const lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__4 = (const lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__4_value;
static const lean_string_object l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__5 = (const lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__5_value;
static const lean_string_object l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "attrInstance"};
static const lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__6 = (const lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__6_value;
static const lean_ctor_object l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_cbvSimprocEval___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__7_value_aux_0),((lean_object*)&l_Lean_Parser_cbvSimprocEval___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__7_value_aux_1),((lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__7_value_aux_2),((lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__10_value),LEAN_SCALAR_PTR_LITERAL(32, 164, 20, 104, 12, 221, 204, 110)}};
static const lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__7 = (const lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Builtin__cbv__simproc_________x28___x29_x3a_x3d____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "builtin_cbv_simproc_decl"};
static const lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Builtin__cbv__simproc_________x28___x29_x3a_x3d____1___closed__0 = (const lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Builtin__cbv__simproc_________x28___x29_x3a_x3d____1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Builtin__cbv__simproc_________x28___x29_x3a_x3d____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Builtin__cbv__simproc_________x28___x29_x3a_x3d____1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__19(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_54_ = ((lean_object*)(l_Lean_Parser_cbvSimprocEval));
v___x_55_ = l_Lean_Parser_Tactic_simpPost;
v___x_56_ = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__18));
v___x_57_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_57_, 0, v___x_56_);
lean_ctor_set(v___x_57_, 1, v___x_55_);
lean_ctor_set(v___x_57_, 2, v___x_54_);
return v___x_57_;
}
}
static lean_object* _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__20(void){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_58_ = lean_obj_once(&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__19, &l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__19_once, _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__19);
v___x_59_ = l_Lean_Parser_Tactic_simpPre;
v___x_60_ = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__18));
v___x_61_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_61_, 0, v___x_60_);
lean_ctor_set(v___x_61_, 1, v___x_59_);
lean_ctor_set(v___x_61_, 2, v___x_58_);
return v___x_61_;
}
}
static lean_object* _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__21(void){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_62_ = lean_obj_once(&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__20, &l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__20_once, _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__20);
v___x_63_ = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__5));
v___x_64_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_64_, 0, v___x_63_);
lean_ctor_set(v___x_64_, 1, v___x_62_);
return v___x_64_;
}
}
static lean_object* _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__22(void){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_65_ = lean_obj_once(&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__21, &l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__21_once, _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__21);
v___x_66_ = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__16));
v___x_67_ = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3));
v___x_68_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_68_, 0, v___x_67_);
lean_ctor_set(v___x_68_, 1, v___x_66_);
lean_ctor_set(v___x_68_, 2, v___x_65_);
return v___x_68_;
}
}
static lean_object* _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__26(void){
_start:
{
lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_74_ = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__25));
v___x_75_ = lean_obj_once(&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__22, &l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__22_once, _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__22);
v___x_76_ = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3));
v___x_77_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_77_, 0, v___x_76_);
lean_ctor_set(v___x_77_, 1, v___x_75_);
lean_ctor_set(v___x_77_, 2, v___x_74_);
return v___x_77_;
}
}
static lean_object* _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__29(void){
_start:
{
lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_81_ = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__28));
v___x_82_ = lean_obj_once(&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__26, &l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__26_once, _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__26);
v___x_83_ = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3));
v___x_84_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_84_, 0, v___x_83_);
lean_ctor_set(v___x_84_, 1, v___x_82_);
lean_ctor_set(v___x_84_, 2, v___x_81_);
return v___x_84_;
}
}
static lean_object* _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__33(void){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_91_ = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__32));
v___x_92_ = lean_obj_once(&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__29, &l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__29_once, _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__29);
v___x_93_ = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3));
v___x_94_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_94_, 0, v___x_93_);
lean_ctor_set(v___x_94_, 1, v___x_92_);
lean_ctor_set(v___x_94_, 2, v___x_91_);
return v___x_94_;
}
}
static lean_object* _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__36(void){
_start:
{
lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_98_ = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__35));
v___x_99_ = lean_obj_once(&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__33, &l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__33_once, _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__33);
v___x_100_ = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3));
v___x_101_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
lean_ctor_set(v___x_101_, 1, v___x_99_);
lean_ctor_set(v___x_101_, 2, v___x_98_);
return v___x_101_;
}
}
static lean_object* _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__39(void){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_105_ = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__38));
v___x_106_ = lean_obj_once(&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__36, &l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__36_once, _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__36);
v___x_107_ = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3));
v___x_108_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_108_, 0, v___x_107_);
lean_ctor_set(v___x_108_, 1, v___x_106_);
lean_ctor_set(v___x_108_, 2, v___x_105_);
return v___x_108_;
}
}
static lean_object* _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__40(void){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_109_ = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__32));
v___x_110_ = lean_obj_once(&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__39, &l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__39_once, _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__39);
v___x_111_ = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3));
v___x_112_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_112_, 0, v___x_111_);
lean_ctor_set(v___x_112_, 1, v___x_110_);
lean_ctor_set(v___x_112_, 2, v___x_109_);
return v___x_112_;
}
}
static lean_object* _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__41(void){
_start:
{
lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_113_ = lean_obj_once(&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__40, &l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__40_once, _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__40);
v___x_114_ = lean_unsigned_to_nat(1022u);
v___x_115_ = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__1));
v___x_116_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_116_, 0, v___x_115_);
lean_ctor_set(v___x_116_, 1, v___x_114_);
lean_ctor_set(v___x_116_, 2, v___x_113_);
return v___x_116_;
}
}
static lean_object* _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d__(void){
_start:
{
lean_object* v___x_117_; 
v___x_117_ = lean_obj_once(&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__41, &l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__41_once, _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__41);
return v___x_117_;
}
}
static lean_object* _init_l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__5(void){
_start:
{
lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_171_ = lean_obj_once(&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__21, &l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__21_once, _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__21);
v___x_172_ = ((lean_object*)(l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__4));
v___x_173_ = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3));
v___x_174_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_174_, 0, v___x_173_);
lean_ctor_set(v___x_174_, 1, v___x_172_);
lean_ctor_set(v___x_174_, 2, v___x_171_);
return v___x_174_;
}
}
static lean_object* _init_l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__6(void){
_start:
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_175_ = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__25));
v___x_176_ = lean_obj_once(&l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__5, &l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__5_once, _init_l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__5);
v___x_177_ = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3));
v___x_178_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_178_, 0, v___x_177_);
lean_ctor_set(v___x_178_, 1, v___x_176_);
lean_ctor_set(v___x_178_, 2, v___x_175_);
return v___x_178_;
}
}
static lean_object* _init_l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__7(void){
_start:
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_179_ = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__28));
v___x_180_ = lean_obj_once(&l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__6, &l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__6_once, _init_l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__6);
v___x_181_ = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3));
v___x_182_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_182_, 0, v___x_181_);
lean_ctor_set(v___x_182_, 1, v___x_180_);
lean_ctor_set(v___x_182_, 2, v___x_179_);
return v___x_182_;
}
}
static lean_object* _init_l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__8(void){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_183_ = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__32));
v___x_184_ = lean_obj_once(&l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__7, &l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__7_once, _init_l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__7);
v___x_185_ = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3));
v___x_186_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_186_, 0, v___x_185_);
lean_ctor_set(v___x_186_, 1, v___x_184_);
lean_ctor_set(v___x_186_, 2, v___x_183_);
return v___x_186_;
}
}
static lean_object* _init_l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__9(void){
_start:
{
lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_187_ = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__35));
v___x_188_ = lean_obj_once(&l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__8, &l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__8_once, _init_l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__8);
v___x_189_ = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3));
v___x_190_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_190_, 0, v___x_189_);
lean_ctor_set(v___x_190_, 1, v___x_188_);
lean_ctor_set(v___x_190_, 2, v___x_187_);
return v___x_190_;
}
}
static lean_object* _init_l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__10(void){
_start:
{
lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_191_ = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__38));
v___x_192_ = lean_obj_once(&l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__9, &l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__9_once, _init_l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__9);
v___x_193_ = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3));
v___x_194_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_194_, 0, v___x_193_);
lean_ctor_set(v___x_194_, 1, v___x_192_);
lean_ctor_set(v___x_194_, 2, v___x_191_);
return v___x_194_;
}
}
static lean_object* _init_l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__11(void){
_start:
{
lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_195_ = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__32));
v___x_196_ = lean_obj_once(&l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__10, &l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__10_once, _init_l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__10);
v___x_197_ = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3));
v___x_198_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_198_, 0, v___x_197_);
lean_ctor_set(v___x_198_, 1, v___x_196_);
lean_ctor_set(v___x_198_, 2, v___x_195_);
return v___x_198_;
}
}
static lean_object* _init_l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__12(void){
_start:
{
lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_199_ = lean_obj_once(&l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__11, &l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__11_once, _init_l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__11);
v___x_200_ = lean_unsigned_to_nat(1022u);
v___x_201_ = ((lean_object*)(l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__1));
v___x_202_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_202_, 0, v___x_201_);
lean_ctor_set(v___x_202_, 1, v___x_200_);
lean_ctor_set(v___x_202_, 2, v___x_199_);
return v___x_202_;
}
}
static lean_object* _init_l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d__(void){
_start:
{
lean_object* v___x_203_; 
v___x_203_ = lean_obj_once(&l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__12, &l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__12_once, _init_l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__12);
return v___x_203_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_cbvSimprocAttr___closed__5(void){
_start:
{
lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_309_ = lean_obj_once(&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__21, &l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__21_once, _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__21);
v___x_310_ = ((lean_object*)(l_Lean_Parser_Attr_cbvSimprocAttr___closed__4));
v___x_311_ = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3));
v___x_312_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_312_, 0, v___x_311_);
lean_ctor_set(v___x_312_, 1, v___x_310_);
lean_ctor_set(v___x_312_, 2, v___x_309_);
return v___x_312_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_cbvSimprocAttr___closed__6(void){
_start:
{
lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_313_ = lean_obj_once(&l_Lean_Parser_Attr_cbvSimprocAttr___closed__5, &l_Lean_Parser_Attr_cbvSimprocAttr___closed__5_once, _init_l_Lean_Parser_Attr_cbvSimprocAttr___closed__5);
v___x_314_ = lean_unsigned_to_nat(1022u);
v___x_315_ = ((lean_object*)(l_Lean_Parser_Attr_cbvSimprocAttr___closed__2));
v___x_316_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_316_, 0, v___x_315_);
lean_ctor_set(v___x_316_, 1, v___x_314_);
lean_ctor_set(v___x_316_, 2, v___x_313_);
return v___x_316_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_cbvSimprocAttr(void){
_start:
{
lean_object* v___x_317_; 
v___x_317_ = lean_obj_once(&l_Lean_Parser_Attr_cbvSimprocAttr___closed__6, &l_Lean_Parser_Attr_cbvSimprocAttr___closed__6_once, _init_l_Lean_Parser_Attr_cbvSimprocAttr___closed__6);
return v___x_317_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__4(void){
_start:
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_328_ = lean_obj_once(&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__21, &l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__21_once, _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__21);
v___x_329_ = ((lean_object*)(l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__3));
v___x_330_ = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3));
v___x_331_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_331_, 0, v___x_330_);
lean_ctor_set(v___x_331_, 1, v___x_329_);
lean_ctor_set(v___x_331_, 2, v___x_328_);
return v___x_331_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__5(void){
_start:
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_332_ = lean_obj_once(&l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__4, &l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__4_once, _init_l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__4);
v___x_333_ = lean_unsigned_to_nat(1022u);
v___x_334_ = ((lean_object*)(l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__1));
v___x_335_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
lean_ctor_set(v___x_335_, 1, v___x_333_);
lean_ctor_set(v___x_335_, 2, v___x_332_);
return v___x_335_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_cbvSimprocBuiltinAttr(void){
_start:
{
lean_object* v___x_336_; 
v___x_336_ = lean_obj_once(&l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__5, &l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__5_once, _init_l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__5);
return v___x_336_;
}
}
static lean_object* _init_l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__28(void){
_start:
{
lean_object* v___x_387_; 
v___x_387_ = l_Array_mkArray0(lean_box(0));
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1(lean_object* v_x_395_, lean_object* v_a_396_, lean_object* v_a_397_){
_start:
{
lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___y_401_; lean_object* v___y_402_; lean_object* v___y_403_; lean_object* v___y_404_; lean_object* v___y_405_; lean_object* v___y_406_; lean_object* v___y_407_; lean_object* v___y_408_; lean_object* v___y_409_; lean_object* v___y_410_; lean_object* v___y_411_; lean_object* v___y_412_; lean_object* v_doc_x3f_456_; lean_object* v___y_457_; lean_object* v___y_458_; lean_object* v___x_481_; uint8_t v___x_482_; 
v___x_398_ = ((lean_object*)(l_Lean_Parser_cbvSimprocEval___closed__1));
v___x_399_ = ((lean_object*)(l_Lean_Parser_cbvSimprocEval___closed__2));
v___x_481_ = ((lean_object*)(l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__1));
lean_inc(v_x_395_);
v___x_482_ = l_Lean_Syntax_isOfKind(v_x_395_, v___x_481_);
if (v___x_482_ == 0)
{
lean_object* v___x_483_; lean_object* v___x_484_; 
lean_dec(v_x_395_);
v___x_483_ = lean_box(1);
v___x_484_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_484_, 0, v___x_483_);
lean_ctor_set(v___x_484_, 1, v_a_397_);
return v___x_484_;
}
else
{
lean_object* v___x_485_; lean_object* v___x_486_; uint8_t v___x_487_; 
v___x_485_ = lean_unsigned_to_nat(0u);
v___x_486_ = l_Lean_Syntax_getArg(v_x_395_, v___x_485_);
v___x_487_ = l_Lean_Syntax_isNone(v___x_486_);
if (v___x_487_ == 0)
{
lean_object* v___x_488_; uint8_t v___x_489_; 
v___x_488_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_486_);
v___x_489_ = l_Lean_Syntax_matchesNull(v___x_486_, v___x_488_);
if (v___x_489_ == 0)
{
lean_object* v___x_490_; lean_object* v___x_491_; 
lean_dec(v___x_486_);
lean_dec(v_x_395_);
v___x_490_ = lean_box(1);
v___x_491_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_491_, 0, v___x_490_);
lean_ctor_set(v___x_491_, 1, v_a_397_);
return v___x_491_;
}
else
{
lean_object* v_doc_x3f_492_; lean_object* v___x_493_; uint8_t v___x_494_; 
v_doc_x3f_492_ = l_Lean_Syntax_getArg(v___x_486_, v___x_485_);
lean_dec(v___x_486_);
v___x_493_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__30));
lean_inc(v_doc_x3f_492_);
v___x_494_ = l_Lean_Syntax_isOfKind(v_doc_x3f_492_, v___x_493_);
if (v___x_494_ == 0)
{
lean_object* v___x_495_; lean_object* v___x_496_; 
lean_dec(v_doc_x3f_492_);
lean_dec(v_x_395_);
v___x_495_ = lean_box(1);
v___x_496_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_496_, 0, v___x_495_);
lean_ctor_set(v___x_496_, 1, v_a_397_);
return v___x_496_;
}
else
{
lean_object* v___x_497_; 
v___x_497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_497_, 0, v_doc_x3f_492_);
v_doc_x3f_456_ = v___x_497_;
v___y_457_ = v_a_396_;
v___y_458_ = v_a_397_;
goto v___jp_455_;
}
}
}
else
{
lean_object* v___x_498_; 
lean_dec(v___x_486_);
v___x_498_ = lean_box(0);
v_doc_x3f_456_ = v___x_498_;
v___y_457_ = v_a_396_;
v___y_458_ = v_a_397_;
goto v___jp_455_;
}
}
v___jp_400_:
{
lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
lean_inc_ref(v___y_401_);
v___x_413_ = l_Array_append___redArg(v___y_401_, v___y_412_);
lean_dec_ref(v___y_412_);
lean_inc(v___y_407_);
lean_inc(v___y_403_);
v___x_414_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_414_, 0, v___y_403_);
lean_ctor_set(v___x_414_, 1, v___y_407_);
lean_ctor_set(v___x_414_, 2, v___x_413_);
lean_inc(v___y_407_);
lean_inc(v___y_403_);
v___x_415_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_415_, 0, v___y_403_);
lean_ctor_set(v___x_415_, 1, v___y_407_);
lean_ctor_set(v___x_415_, 2, v___y_401_);
v___x_416_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__0));
lean_inc_ref(v___y_406_);
v___x_417_ = l_Lean_Name_mkStr4(v___x_398_, v___x_399_, v___y_406_, v___x_416_);
lean_inc(v___y_403_);
v___x_418_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_418_, 0, v___y_403_);
lean_ctor_set(v___x_418_, 1, v___x_416_);
lean_inc(v___y_403_);
v___x_419_ = l_Lean_Syntax_node1(v___y_403_, v___x_417_, v___x_418_);
lean_inc(v___y_407_);
lean_inc(v___y_403_);
v___x_420_ = l_Lean_Syntax_node1(v___y_403_, v___y_407_, v___x_419_);
lean_inc_ref_n(v___x_415_, 5);
lean_inc(v___y_403_);
v___x_421_ = l_Lean_Syntax_node7(v___y_403_, v___y_410_, v___x_414_, v___x_415_, v___x_415_, v___x_415_, v___x_420_, v___x_415_, v___x_415_);
v___x_422_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__1));
lean_inc_ref(v___y_406_);
v___x_423_ = l_Lean_Name_mkStr4(v___x_398_, v___x_399_, v___y_406_, v___x_422_);
v___x_424_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__2));
lean_inc(v___y_403_);
v___x_425_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_425_, 0, v___y_403_);
lean_ctor_set(v___x_425_, 1, v___x_424_);
v___x_426_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__3));
lean_inc_ref(v___y_406_);
v___x_427_ = l_Lean_Name_mkStr4(v___x_398_, v___x_399_, v___y_406_, v___x_426_);
lean_inc_ref(v___x_415_);
lean_inc(v___y_405_);
lean_inc(v___y_403_);
v___x_428_ = l_Lean_Syntax_node2(v___y_403_, v___x_427_, v___y_405_, v___x_415_);
v___x_429_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__4));
lean_inc_ref(v___y_406_);
v___x_430_ = l_Lean_Name_mkStr4(v___x_398_, v___x_399_, v___y_406_, v___x_429_);
v___x_431_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__7));
v___x_432_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__8));
lean_inc(v___y_403_);
v___x_433_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_433_, 0, v___y_403_);
lean_ctor_set(v___x_433_, 1, v___x_432_);
v___x_434_ = lean_mk_syntax_ident(v___y_404_);
lean_inc(v___y_403_);
v___x_435_ = l_Lean_Syntax_node2(v___y_403_, v___x_431_, v___x_433_, v___x_434_);
lean_inc(v___y_407_);
lean_inc(v___y_403_);
v___x_436_ = l_Lean_Syntax_node1(v___y_403_, v___y_407_, v___x_435_);
lean_inc_ref(v___x_415_);
lean_inc(v___y_403_);
v___x_437_ = l_Lean_Syntax_node2(v___y_403_, v___x_430_, v___x_415_, v___x_436_);
v___x_438_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__9));
v___x_439_ = l_Lean_Name_mkStr4(v___x_398_, v___x_399_, v___y_406_, v___x_438_);
v___x_440_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__10));
lean_inc(v___y_403_);
v___x_441_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_441_, 0, v___y_403_);
lean_ctor_set(v___x_441_, 1, v___x_440_);
v___x_442_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__13));
lean_inc_ref_n(v___x_415_, 2);
lean_inc(v___y_403_);
v___x_443_ = l_Lean_Syntax_node2(v___y_403_, v___x_442_, v___x_415_, v___x_415_);
lean_inc_ref(v___x_415_);
lean_inc(v___y_403_);
v___x_444_ = l_Lean_Syntax_node4(v___y_403_, v___x_439_, v___x_441_, v___y_408_, v___x_443_, v___x_415_);
lean_inc(v___y_403_);
v___x_445_ = l_Lean_Syntax_node5(v___y_403_, v___x_423_, v___x_425_, v___x_428_, v___x_437_, v___x_444_, v___x_415_);
lean_inc(v___y_403_);
v___x_446_ = l_Lean_Syntax_node2(v___y_403_, v___y_402_, v___x_421_, v___x_445_);
v___x_447_ = ((lean_object*)(l_Lean_Parser_cbvSimprocPattern___closed__1));
v___x_448_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__14));
lean_inc(v___y_403_);
v___x_449_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_449_, 0, v___y_403_);
lean_ctor_set(v___x_449_, 1, v___x_448_);
v___x_450_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__15));
lean_inc(v___y_403_);
v___x_451_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_451_, 0, v___y_403_);
lean_ctor_set(v___x_451_, 1, v___x_450_);
lean_inc(v___y_403_);
v___x_452_ = l_Lean_Syntax_node4(v___y_403_, v___x_447_, v___x_449_, v___y_409_, v___x_451_, v___y_405_);
v___x_453_ = l_Lean_Syntax_node2(v___y_403_, v___y_407_, v___x_446_, v___x_452_);
v___x_454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_454_, 0, v___x_453_);
lean_ctor_set(v___x_454_, 1, v___y_411_);
return v___x_454_;
}
v___jp_455_:
{
lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; uint8_t v___x_462_; 
v___x_459_ = lean_unsigned_to_nat(2u);
v___x_460_ = l_Lean_Syntax_getArg(v_x_395_, v___x_459_);
v___x_461_ = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__24));
lean_inc(v___x_460_);
v___x_462_ = l_Lean_Syntax_isOfKind(v___x_460_, v___x_461_);
if (v___x_462_ == 0)
{
lean_object* v___x_463_; lean_object* v___x_464_; 
lean_dec(v___x_460_);
lean_dec(v_doc_x3f_456_);
lean_dec(v_x_395_);
v___x_463_ = lean_box(1);
v___x_464_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_464_, 0, v___x_463_);
lean_ctor_set(v___x_464_, 1, v___y_458_);
return v___x_464_;
}
else
{
lean_object* v_ref_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v_simprocType_470_; uint8_t v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v_ref_465_ = lean_ctor_get(v___y_457_, 5);
v___x_466_ = lean_unsigned_to_nat(4u);
v___x_467_ = l_Lean_Syntax_getArg(v_x_395_, v___x_466_);
v___x_468_ = lean_unsigned_to_nat(7u);
v___x_469_ = l_Lean_Syntax_getArg(v_x_395_, v___x_468_);
lean_dec(v_x_395_);
v_simprocType_470_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__20));
v___x_471_ = 0;
v___x_472_ = l_Lean_SourceInfo_fromRef(v_ref_465_, v___x_471_);
v___x_473_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__22));
v___x_474_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__23));
v___x_475_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__25));
v___x_476_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__27));
v___x_477_ = lean_obj_once(&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__28, &l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__28_once, _init_l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__28);
if (lean_obj_tag(v_doc_x3f_456_) == 1)
{
lean_object* v_val_478_; lean_object* v___x_479_; 
v_val_478_ = lean_ctor_get(v_doc_x3f_456_, 0);
lean_inc(v_val_478_);
lean_dec_ref(v_doc_x3f_456_);
v___x_479_ = l_Array_mkArray1___redArg(v_val_478_);
v___y_401_ = v___x_477_;
v___y_402_ = v___x_475_;
v___y_403_ = v___x_472_;
v___y_404_ = v_simprocType_470_;
v___y_405_ = v___x_460_;
v___y_406_ = v___x_474_;
v___y_407_ = v___x_473_;
v___y_408_ = v___x_469_;
v___y_409_ = v___x_467_;
v___y_410_ = v___x_476_;
v___y_411_ = v___y_458_;
v___y_412_ = v___x_479_;
goto v___jp_400_;
}
else
{
lean_object* v___x_480_; 
lean_dec(v_doc_x3f_456_);
v___x_480_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__29));
v___y_401_ = v___x_477_;
v___y_402_ = v___x_475_;
v___y_403_ = v___x_472_;
v___y_404_ = v_simprocType_470_;
v___y_405_ = v___x_460_;
v___y_406_ = v___x_474_;
v___y_407_ = v___x_473_;
v___y_408_ = v___x_469_;
v___y_409_ = v___x_467_;
v___y_410_ = v___x_476_;
v___y_411_ = v___y_458_;
v___y_412_ = v___x_480_;
goto v___jp_400_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___boxed(lean_object* v_x_499_, lean_object* v_a_500_, lean_object* v_a_501_){
_start:
{
lean_object* v_res_502_; 
v_res_502_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1(v_x_499_, v_a_500_, v_a_501_);
lean_dec_ref(v_a_500_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d____1(lean_object* v_x_504_, lean_object* v_a_505_, lean_object* v_a_506_){
_start:
{
lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___y_510_; lean_object* v___y_511_; lean_object* v___y_512_; lean_object* v___y_513_; lean_object* v___y_514_; lean_object* v___y_515_; lean_object* v___y_516_; lean_object* v___y_517_; lean_object* v___y_518_; lean_object* v___y_519_; lean_object* v___y_520_; lean_object* v___y_521_; lean_object* v_doc_x3f_560_; lean_object* v___y_561_; lean_object* v___y_562_; lean_object* v___x_585_; uint8_t v___x_586_; 
v___x_507_ = ((lean_object*)(l_Lean_Parser_cbvSimprocEval___closed__1));
v___x_508_ = ((lean_object*)(l_Lean_Parser_cbvSimprocEval___closed__2));
v___x_585_ = ((lean_object*)(l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__1));
lean_inc(v_x_504_);
v___x_586_ = l_Lean_Syntax_isOfKind(v_x_504_, v___x_585_);
if (v___x_586_ == 0)
{
lean_object* v___x_587_; lean_object* v___x_588_; 
lean_dec(v_x_504_);
v___x_587_ = lean_box(1);
v___x_588_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_588_, 0, v___x_587_);
lean_ctor_set(v___x_588_, 1, v_a_506_);
return v___x_588_;
}
else
{
lean_object* v___x_589_; lean_object* v___x_590_; uint8_t v___x_591_; 
v___x_589_ = lean_unsigned_to_nat(0u);
v___x_590_ = l_Lean_Syntax_getArg(v_x_504_, v___x_589_);
v___x_591_ = l_Lean_Syntax_isNone(v___x_590_);
if (v___x_591_ == 0)
{
lean_object* v___x_592_; uint8_t v___x_593_; 
v___x_592_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_590_);
v___x_593_ = l_Lean_Syntax_matchesNull(v___x_590_, v___x_592_);
if (v___x_593_ == 0)
{
lean_object* v___x_594_; lean_object* v___x_595_; 
lean_dec(v___x_590_);
lean_dec(v_x_504_);
v___x_594_ = lean_box(1);
v___x_595_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_595_, 0, v___x_594_);
lean_ctor_set(v___x_595_, 1, v_a_506_);
return v___x_595_;
}
else
{
lean_object* v_doc_x3f_596_; lean_object* v___x_597_; uint8_t v___x_598_; 
v_doc_x3f_596_ = l_Lean_Syntax_getArg(v___x_590_, v___x_589_);
lean_dec(v___x_590_);
v___x_597_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__30));
lean_inc(v_doc_x3f_596_);
v___x_598_ = l_Lean_Syntax_isOfKind(v_doc_x3f_596_, v___x_597_);
if (v___x_598_ == 0)
{
lean_object* v___x_599_; lean_object* v___x_600_; 
lean_dec(v_doc_x3f_596_);
lean_dec(v_x_504_);
v___x_599_ = lean_box(1);
v___x_600_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_600_, 0, v___x_599_);
lean_ctor_set(v___x_600_, 1, v_a_506_);
return v___x_600_;
}
else
{
lean_object* v___x_601_; 
v___x_601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_601_, 0, v_doc_x3f_596_);
v_doc_x3f_560_ = v___x_601_;
v___y_561_ = v_a_505_;
v___y_562_ = v_a_506_;
goto v___jp_559_;
}
}
}
else
{
lean_object* v___x_602_; 
lean_dec(v___x_590_);
v___x_602_ = lean_box(0);
v_doc_x3f_560_ = v___x_602_;
v___y_561_ = v_a_505_;
v___y_562_ = v_a_506_;
goto v___jp_559_;
}
}
v___jp_509_:
{
lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
lean_inc_ref(v___y_514_);
v___x_522_ = l_Array_append___redArg(v___y_514_, v___y_521_);
lean_dec_ref(v___y_521_);
lean_inc(v___y_510_);
lean_inc(v___y_520_);
v___x_523_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_523_, 0, v___y_520_);
lean_ctor_set(v___x_523_, 1, v___y_510_);
lean_ctor_set(v___x_523_, 2, v___x_522_);
lean_inc(v___y_510_);
lean_inc(v___y_520_);
v___x_524_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_524_, 0, v___y_520_);
lean_ctor_set(v___x_524_, 1, v___y_510_);
lean_ctor_set(v___x_524_, 2, v___y_514_);
lean_inc_ref_n(v___x_524_, 6);
lean_inc(v___y_520_);
v___x_525_ = l_Lean_Syntax_node7(v___y_520_, v___y_517_, v___x_523_, v___x_524_, v___x_524_, v___x_524_, v___x_524_, v___x_524_, v___x_524_);
v___x_526_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__1));
lean_inc_ref(v___y_516_);
v___x_527_ = l_Lean_Name_mkStr4(v___x_507_, v___x_508_, v___y_516_, v___x_526_);
v___x_528_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__2));
lean_inc(v___y_520_);
v___x_529_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_529_, 0, v___y_520_);
lean_ctor_set(v___x_529_, 1, v___x_528_);
v___x_530_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__3));
lean_inc_ref(v___y_516_);
v___x_531_ = l_Lean_Name_mkStr4(v___x_507_, v___x_508_, v___y_516_, v___x_530_);
lean_inc_ref(v___x_524_);
lean_inc(v___y_515_);
lean_inc(v___y_520_);
v___x_532_ = l_Lean_Syntax_node2(v___y_520_, v___x_531_, v___y_515_, v___x_524_);
v___x_533_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__4));
lean_inc_ref(v___y_516_);
v___x_534_ = l_Lean_Name_mkStr4(v___x_507_, v___x_508_, v___y_516_, v___x_533_);
v___x_535_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__7));
v___x_536_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__8));
lean_inc(v___y_520_);
v___x_537_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_537_, 0, v___y_520_);
lean_ctor_set(v___x_537_, 1, v___x_536_);
v___x_538_ = lean_mk_syntax_ident(v___y_519_);
lean_inc(v___y_520_);
v___x_539_ = l_Lean_Syntax_node2(v___y_520_, v___x_535_, v___x_537_, v___x_538_);
lean_inc(v___y_510_);
lean_inc(v___y_520_);
v___x_540_ = l_Lean_Syntax_node1(v___y_520_, v___y_510_, v___x_539_);
lean_inc_ref(v___x_524_);
lean_inc(v___y_520_);
v___x_541_ = l_Lean_Syntax_node2(v___y_520_, v___x_534_, v___x_524_, v___x_540_);
v___x_542_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__9));
v___x_543_ = l_Lean_Name_mkStr4(v___x_507_, v___x_508_, v___y_516_, v___x_542_);
v___x_544_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__10));
lean_inc(v___y_520_);
v___x_545_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_545_, 0, v___y_520_);
lean_ctor_set(v___x_545_, 1, v___x_544_);
v___x_546_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__13));
lean_inc_ref_n(v___x_524_, 2);
lean_inc(v___y_520_);
v___x_547_ = l_Lean_Syntax_node2(v___y_520_, v___x_546_, v___x_524_, v___x_524_);
lean_inc_ref(v___x_524_);
lean_inc(v___y_520_);
v___x_548_ = l_Lean_Syntax_node4(v___y_520_, v___x_543_, v___x_545_, v___y_518_, v___x_547_, v___x_524_);
lean_inc(v___y_520_);
v___x_549_ = l_Lean_Syntax_node5(v___y_520_, v___x_527_, v___x_529_, v___x_532_, v___x_541_, v___x_548_, v___x_524_);
lean_inc(v___y_520_);
v___x_550_ = l_Lean_Syntax_node2(v___y_520_, v___y_513_, v___x_525_, v___x_549_);
v___x_551_ = ((lean_object*)(l_Lean_Parser_cbvSimprocPatternBuiltin___closed__1));
v___x_552_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__0));
lean_inc(v___y_520_);
v___x_553_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_553_, 0, v___y_520_);
lean_ctor_set(v___x_553_, 1, v___x_552_);
v___x_554_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__15));
lean_inc(v___y_520_);
v___x_555_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_555_, 0, v___y_520_);
lean_ctor_set(v___x_555_, 1, v___x_554_);
lean_inc(v___y_520_);
v___x_556_ = l_Lean_Syntax_node4(v___y_520_, v___x_551_, v___x_553_, v___y_512_, v___x_555_, v___y_515_);
v___x_557_ = l_Lean_Syntax_node2(v___y_520_, v___y_510_, v___x_550_, v___x_556_);
v___x_558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_558_, 0, v___x_557_);
lean_ctor_set(v___x_558_, 1, v___y_511_);
return v___x_558_;
}
v___jp_559_:
{
lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; uint8_t v___x_566_; 
v___x_563_ = lean_unsigned_to_nat(2u);
v___x_564_ = l_Lean_Syntax_getArg(v_x_504_, v___x_563_);
v___x_565_ = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__24));
lean_inc(v___x_564_);
v___x_566_ = l_Lean_Syntax_isOfKind(v___x_564_, v___x_565_);
if (v___x_566_ == 0)
{
lean_object* v___x_567_; lean_object* v___x_568_; 
lean_dec(v___x_564_);
lean_dec(v_doc_x3f_560_);
lean_dec(v_x_504_);
v___x_567_ = lean_box(1);
v___x_568_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_568_, 0, v___x_567_);
lean_ctor_set(v___x_568_, 1, v___y_562_);
return v___x_568_;
}
else
{
lean_object* v_ref_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v_simprocType_574_; uint8_t v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
v_ref_569_ = lean_ctor_get(v___y_561_, 5);
v___x_570_ = lean_unsigned_to_nat(4u);
v___x_571_ = l_Lean_Syntax_getArg(v_x_504_, v___x_570_);
v___x_572_ = lean_unsigned_to_nat(7u);
v___x_573_ = l_Lean_Syntax_getArg(v_x_504_, v___x_572_);
lean_dec(v_x_504_);
v_simprocType_574_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__20));
v___x_575_ = 0;
v___x_576_ = l_Lean_SourceInfo_fromRef(v_ref_569_, v___x_575_);
v___x_577_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__22));
v___x_578_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__23));
v___x_579_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__25));
v___x_580_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__27));
v___x_581_ = lean_obj_once(&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__28, &l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__28_once, _init_l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__28);
if (lean_obj_tag(v_doc_x3f_560_) == 1)
{
lean_object* v_val_582_; lean_object* v___x_583_; 
v_val_582_ = lean_ctor_get(v_doc_x3f_560_, 0);
lean_inc(v_val_582_);
lean_dec_ref(v_doc_x3f_560_);
v___x_583_ = l_Array_mkArray1___redArg(v_val_582_);
v___y_510_ = v___x_577_;
v___y_511_ = v___y_562_;
v___y_512_ = v___x_571_;
v___y_513_ = v___x_579_;
v___y_514_ = v___x_581_;
v___y_515_ = v___x_564_;
v___y_516_ = v___x_578_;
v___y_517_ = v___x_580_;
v___y_518_ = v___x_573_;
v___y_519_ = v_simprocType_574_;
v___y_520_ = v___x_576_;
v___y_521_ = v___x_583_;
goto v___jp_509_;
}
else
{
lean_object* v___x_584_; 
lean_dec(v_doc_x3f_560_);
v___x_584_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__29));
v___y_510_ = v___x_577_;
v___y_511_ = v___y_562_;
v___y_512_ = v___x_571_;
v___y_513_ = v___x_579_;
v___y_514_ = v___x_581_;
v___y_515_ = v___x_564_;
v___y_516_ = v___x_578_;
v___y_517_ = v___x_580_;
v___y_518_ = v___x_573_;
v___y_519_ = v_simprocType_574_;
v___y_520_ = v___x_576_;
v___y_521_ = v___x_584_;
goto v___jp_509_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d____1___boxed(lean_object* v_x_603_, lean_object* v_a_604_, lean_object* v_a_605_){
_start:
{
lean_object* v_res_606_; 
v_res_606_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d____1(v_x_603_, v_a_604_, v_a_605_);
lean_dec_ref(v_a_604_);
return v_res_606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1(lean_object* v_x_623_, lean_object* v_a_624_, lean_object* v_a_625_){
_start:
{
lean_object* v___y_627_; lean_object* v___y_628_; lean_object* v___y_629_; lean_object* v___y_630_; lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; uint8_t v___x_655_; 
v___x_652_ = ((lean_object*)(l_Lean_Parser_cbvSimprocEval___closed__1));
v___x_653_ = ((lean_object*)(l_Lean_Parser_cbvSimprocEval___closed__2));
v___x_654_ = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__1));
lean_inc(v_x_623_);
v___x_655_ = l_Lean_Syntax_isOfKind(v_x_623_, v___x_654_);
if (v___x_655_ == 0)
{
lean_object* v___x_656_; lean_object* v___x_657_; 
lean_dec(v_x_623_);
v___x_656_ = lean_box(1);
v___x_657_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_657_, 0, v___x_656_);
lean_ctor_set(v___x_657_, 1, v_a_625_);
return v___x_657_;
}
else
{
lean_object* v___x_658_; lean_object* v___y_660_; lean_object* v___y_661_; lean_object* v___y_662_; lean_object* v___y_663_; lean_object* v___y_664_; lean_object* v___y_665_; lean_object* v___y_666_; lean_object* v___y_667_; lean_object* v___y_668_; lean_object* v___y_669_; lean_object* v___y_670_; lean_object* v___y_671_; lean_object* v___y_697_; lean_object* v___y_698_; lean_object* v_phase_x3f_699_; lean_object* v___y_700_; lean_object* v___y_701_; lean_object* v_doc_x3f_723_; lean_object* v___y_724_; lean_object* v___y_725_; lean_object* v___x_741_; uint8_t v___x_742_; 
v___x_658_ = lean_unsigned_to_nat(0u);
v___x_741_ = l_Lean_Syntax_getArg(v_x_623_, v___x_658_);
v___x_742_ = l_Lean_Syntax_isNone(v___x_741_);
if (v___x_742_ == 0)
{
lean_object* v___x_743_; uint8_t v___x_744_; 
v___x_743_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_741_);
v___x_744_ = l_Lean_Syntax_matchesNull(v___x_741_, v___x_743_);
if (v___x_744_ == 0)
{
lean_object* v___x_745_; lean_object* v___x_746_; 
lean_dec(v___x_741_);
lean_dec(v_x_623_);
v___x_745_ = lean_box(1);
v___x_746_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_746_, 0, v___x_745_);
lean_ctor_set(v___x_746_, 1, v_a_625_);
return v___x_746_;
}
else
{
lean_object* v_doc_x3f_747_; lean_object* v___x_748_; uint8_t v___x_749_; 
v_doc_x3f_747_ = l_Lean_Syntax_getArg(v___x_741_, v___x_658_);
lean_dec(v___x_741_);
v___x_748_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__30));
lean_inc(v_doc_x3f_747_);
v___x_749_ = l_Lean_Syntax_isOfKind(v_doc_x3f_747_, v___x_748_);
if (v___x_749_ == 0)
{
lean_object* v___x_750_; lean_object* v___x_751_; 
lean_dec(v_doc_x3f_747_);
lean_dec(v_x_623_);
v___x_750_ = lean_box(1);
v___x_751_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_751_, 0, v___x_750_);
lean_ctor_set(v___x_751_, 1, v_a_625_);
return v___x_751_;
}
else
{
lean_object* v___x_752_; 
v___x_752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_752_, 0, v_doc_x3f_747_);
v_doc_x3f_723_ = v___x_752_;
v___y_724_ = v_a_624_;
v___y_725_ = v_a_625_;
goto v___jp_722_;
}
}
}
else
{
lean_object* v___x_753_; 
lean_dec(v___x_741_);
v___x_753_ = lean_box(0);
v_doc_x3f_723_ = v___x_753_;
v___y_724_ = v_a_624_;
v___y_725_ = v_a_625_;
goto v___jp_722_;
}
v___jp_659_:
{
lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
lean_inc_ref(v___y_669_);
v___x_672_ = l_Array_append___redArg(v___y_669_, v___y_671_);
lean_dec_ref(v___y_671_);
lean_inc(v___y_668_);
lean_inc(v___y_670_);
v___x_673_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_673_, 0, v___y_670_);
lean_ctor_set(v___x_673_, 1, v___y_668_);
lean_ctor_set(v___x_673_, 2, v___x_672_);
v___x_674_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__1));
lean_inc(v___y_670_);
v___x_675_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_675_, 0, v___y_670_);
lean_ctor_set(v___x_675_, 1, v___x_674_);
v___x_676_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__2));
lean_inc(v___y_670_);
v___x_677_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_677_, 0, v___y_670_);
lean_ctor_set(v___x_677_, 1, v___x_676_);
v___x_678_ = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__34));
lean_inc(v___y_670_);
v___x_679_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_679_, 0, v___y_670_);
lean_ctor_set(v___x_679_, 1, v___x_678_);
v___x_680_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__10));
lean_inc(v___y_670_);
v___x_681_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_681_, 0, v___y_670_);
lean_ctor_set(v___x_681_, 1, v___x_680_);
lean_inc(v___y_663_);
lean_inc(v___y_670_);
v___x_682_ = l_Lean_Syntax_node8(v___y_670_, v___y_665_, v___x_673_, v___x_675_, v___y_663_, v___x_677_, v___y_660_, v___x_679_, v___x_681_, v___y_666_);
v___x_683_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__3));
v___x_684_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__4));
lean_inc(v___y_670_);
v___x_685_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_685_, 0, v___y_670_);
lean_ctor_set(v___x_685_, 1, v___x_683_);
v___x_686_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__5));
lean_inc(v___y_670_);
v___x_687_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_687_, 0, v___y_670_);
lean_ctor_set(v___x_687_, 1, v___x_686_);
v___x_688_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__6));
v___x_689_ = l_Lean_Name_mkStr4(v___x_652_, v___x_653_, v___y_661_, v___x_688_);
v___x_690_ = ((lean_object*)(l_Lean_Parser_Attr_cbvSimprocAttr___closed__2));
v___x_691_ = ((lean_object*)(l_Lean_Parser_Attr_cbvSimprocAttr___closed__3));
lean_inc(v___y_670_);
v___x_692_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_692_, 0, v___y_670_);
lean_ctor_set(v___x_692_, 1, v___x_691_);
if (lean_obj_tag(v___y_667_) == 1)
{
lean_object* v_val_693_; lean_object* v___x_694_; 
v_val_693_ = lean_ctor_get(v___y_667_, 0);
lean_inc(v_val_693_);
lean_dec_ref(v___y_667_);
v___x_694_ = l_Array_mkArray1___redArg(v_val_693_);
v___y_627_ = v___y_662_;
v___y_628_ = v___x_682_;
v___y_629_ = v___x_690_;
v___y_630_ = v___x_687_;
v___y_631_ = v___x_692_;
v___y_632_ = v___x_684_;
v___y_633_ = v___y_669_;
v___y_634_ = v___y_663_;
v___y_635_ = v___x_689_;
v___y_636_ = v___y_664_;
v___y_637_ = v___x_685_;
v___y_638_ = v___y_668_;
v___y_639_ = v___y_670_;
v___y_640_ = v___x_694_;
goto v___jp_626_;
}
else
{
lean_object* v___x_695_; 
lean_dec(v___y_667_);
v___x_695_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__29));
v___y_627_ = v___y_662_;
v___y_628_ = v___x_682_;
v___y_629_ = v___x_690_;
v___y_630_ = v___x_687_;
v___y_631_ = v___x_692_;
v___y_632_ = v___x_684_;
v___y_633_ = v___y_669_;
v___y_634_ = v___y_663_;
v___y_635_ = v___x_689_;
v___y_636_ = v___y_664_;
v___y_637_ = v___x_685_;
v___y_638_ = v___y_668_;
v___y_639_ = v___y_670_;
v___y_640_ = v___x_695_;
goto v___jp_626_;
}
}
v___jp_696_:
{
lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; uint8_t v___x_705_; 
v___x_702_ = lean_unsigned_to_nat(4u);
v___x_703_ = l_Lean_Syntax_getArg(v_x_623_, v___x_702_);
v___x_704_ = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__24));
lean_inc(v___x_703_);
v___x_705_ = l_Lean_Syntax_isOfKind(v___x_703_, v___x_704_);
if (v___x_705_ == 0)
{
lean_object* v___x_706_; lean_object* v___x_707_; 
lean_dec(v___x_703_);
lean_dec(v_phase_x3f_699_);
lean_dec(v___y_698_);
lean_dec(v___y_697_);
lean_dec(v_x_623_);
v___x_706_ = lean_box(1);
v___x_707_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_707_, 0, v___x_706_);
lean_ctor_set(v___x_707_, 1, v___y_701_);
return v___x_707_;
}
else
{
lean_object* v_ref_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; uint8_t v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; 
v_ref_708_ = lean_ctor_get(v___y_700_, 5);
v___x_709_ = lean_unsigned_to_nat(6u);
v___x_710_ = l_Lean_Syntax_getArg(v_x_623_, v___x_709_);
v___x_711_ = lean_unsigned_to_nat(9u);
v___x_712_ = l_Lean_Syntax_getArg(v_x_623_, v___x_711_);
lean_dec(v_x_623_);
v___x_713_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__5));
v___x_714_ = 0;
v___x_715_ = l_Lean_SourceInfo_fromRef(v_ref_708_, v___x_714_);
v___x_716_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__22));
v___x_717_ = ((lean_object*)(l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__1));
v___x_718_ = lean_obj_once(&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__28, &l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__28_once, _init_l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__28);
if (lean_obj_tag(v___y_697_) == 1)
{
lean_object* v_val_719_; lean_object* v___x_720_; 
v_val_719_ = lean_ctor_get(v___y_697_, 0);
lean_inc(v_val_719_);
lean_dec_ref(v___y_697_);
v___x_720_ = l_Array_mkArray1___redArg(v_val_719_);
v___y_660_ = v___x_710_;
v___y_661_ = v___x_713_;
v___y_662_ = v___y_701_;
v___y_663_ = v___x_703_;
v___y_664_ = v___y_698_;
v___y_665_ = v___x_717_;
v___y_666_ = v___x_712_;
v___y_667_ = v_phase_x3f_699_;
v___y_668_ = v___x_716_;
v___y_669_ = v___x_718_;
v___y_670_ = v___x_715_;
v___y_671_ = v___x_720_;
goto v___jp_659_;
}
else
{
lean_object* v___x_721_; 
lean_dec(v___y_697_);
v___x_721_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__29));
v___y_660_ = v___x_710_;
v___y_661_ = v___x_713_;
v___y_662_ = v___y_701_;
v___y_663_ = v___x_703_;
v___y_664_ = v___y_698_;
v___y_665_ = v___x_717_;
v___y_666_ = v___x_712_;
v___y_667_ = v_phase_x3f_699_;
v___y_668_ = v___x_716_;
v___y_669_ = v___x_718_;
v___y_670_ = v___x_715_;
v___y_671_ = v___x_721_;
goto v___jp_659_;
}
}
}
v___jp_722_:
{
lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; uint8_t v___x_729_; 
v___x_726_ = lean_unsigned_to_nat(1u);
v___x_727_ = l_Lean_Syntax_getArg(v_x_623_, v___x_726_);
v___x_728_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__7));
lean_inc(v___x_727_);
v___x_729_ = l_Lean_Syntax_isOfKind(v___x_727_, v___x_728_);
if (v___x_729_ == 0)
{
lean_object* v___x_730_; lean_object* v___x_731_; 
lean_dec(v___x_727_);
lean_dec(v_doc_x3f_723_);
lean_dec(v_x_623_);
v___x_730_ = lean_box(1);
v___x_731_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_731_, 0, v___x_730_);
lean_ctor_set(v___x_731_, 1, v___y_725_);
return v___x_731_;
}
else
{
lean_object* v___x_732_; lean_object* v___x_733_; uint8_t v___x_734_; 
v___x_732_ = lean_unsigned_to_nat(3u);
v___x_733_ = l_Lean_Syntax_getArg(v_x_623_, v___x_732_);
v___x_734_ = l_Lean_Syntax_isNone(v___x_733_);
if (v___x_734_ == 0)
{
uint8_t v___x_735_; 
lean_inc(v___x_733_);
v___x_735_ = l_Lean_Syntax_matchesNull(v___x_733_, v___x_726_);
if (v___x_735_ == 0)
{
lean_object* v___x_736_; lean_object* v___x_737_; 
lean_dec(v___x_733_);
lean_dec(v___x_727_);
lean_dec(v_doc_x3f_723_);
lean_dec(v_x_623_);
v___x_736_ = lean_box(1);
v___x_737_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_737_, 0, v___x_736_);
lean_ctor_set(v___x_737_, 1, v___y_725_);
return v___x_737_;
}
else
{
lean_object* v_phase_x3f_738_; lean_object* v___x_739_; 
v_phase_x3f_738_ = l_Lean_Syntax_getArg(v___x_733_, v___x_658_);
lean_dec(v___x_733_);
v___x_739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_739_, 0, v_phase_x3f_738_);
v___y_697_ = v_doc_x3f_723_;
v___y_698_ = v___x_727_;
v_phase_x3f_699_ = v___x_739_;
v___y_700_ = v___y_724_;
v___y_701_ = v___y_725_;
goto v___jp_696_;
}
}
else
{
lean_object* v___x_740_; 
lean_dec(v___x_733_);
v___x_740_ = lean_box(0);
v___y_697_ = v_doc_x3f_723_;
v___y_698_ = v___x_727_;
v_phase_x3f_699_ = v___x_740_;
v___y_700_ = v___y_724_;
v___y_701_ = v___y_725_;
goto v___jp_696_;
}
}
}
}
v___jp_626_:
{
lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_641_ = l_Array_append___redArg(v___y_633_, v___y_640_);
lean_dec_ref(v___y_640_);
lean_inc(v___y_638_);
lean_inc(v___y_639_);
v___x_642_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_642_, 0, v___y_639_);
lean_ctor_set(v___x_642_, 1, v___y_638_);
lean_ctor_set(v___x_642_, 2, v___x_641_);
lean_inc(v___y_639_);
v___x_643_ = l_Lean_Syntax_node2(v___y_639_, v___y_629_, v___y_631_, v___x_642_);
lean_inc(v___y_639_);
v___x_644_ = l_Lean_Syntax_node2(v___y_639_, v___y_635_, v___y_636_, v___x_643_);
lean_inc(v___y_638_);
lean_inc(v___y_639_);
v___x_645_ = l_Lean_Syntax_node1(v___y_639_, v___y_638_, v___x_644_);
v___x_646_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__0));
lean_inc(v___y_639_);
v___x_647_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_647_, 0, v___y_639_);
lean_ctor_set(v___x_647_, 1, v___x_646_);
lean_inc(v___y_638_);
lean_inc(v___y_639_);
v___x_648_ = l_Lean_Syntax_node1(v___y_639_, v___y_638_, v___y_634_);
lean_inc(v___y_639_);
v___x_649_ = l_Lean_Syntax_node5(v___y_639_, v___y_632_, v___y_637_, v___y_630_, v___x_645_, v___x_647_, v___x_648_);
v___x_650_ = l_Lean_Syntax_node2(v___y_639_, v___y_638_, v___y_628_, v___x_649_);
v___x_651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_651_, 0, v___x_650_);
lean_ctor_set(v___x_651_, 1, v___y_627_);
return v___x_651_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___boxed(lean_object* v_x_754_, lean_object* v_a_755_, lean_object* v_a_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1(v_x_754_, v_a_755_, v_a_756_);
lean_dec_ref(v_a_755_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Builtin__cbv__simproc_________x28___x29_x3a_x3d____1(lean_object* v_x_759_, lean_object* v_a_760_, lean_object* v_a_761_){
_start:
{
lean_object* v___y_763_; lean_object* v___y_764_; lean_object* v___y_765_; lean_object* v___y_766_; lean_object* v___y_767_; lean_object* v___y_768_; lean_object* v___y_769_; lean_object* v___y_770_; lean_object* v___y_771_; lean_object* v___y_772_; lean_object* v___y_773_; lean_object* v___y_774_; lean_object* v___y_775_; lean_object* v___y_776_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; uint8_t v___x_791_; 
v___x_788_ = ((lean_object*)(l_Lean_Parser_cbvSimprocEval___closed__1));
v___x_789_ = ((lean_object*)(l_Lean_Parser_cbvSimprocEval___closed__2));
v___x_790_ = ((lean_object*)(l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__1));
lean_inc(v_x_759_);
v___x_791_ = l_Lean_Syntax_isOfKind(v_x_759_, v___x_790_);
if (v___x_791_ == 0)
{
lean_object* v___x_792_; lean_object* v___x_793_; 
lean_dec(v_x_759_);
v___x_792_ = lean_box(1);
v___x_793_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_793_, 0, v___x_792_);
lean_ctor_set(v___x_793_, 1, v_a_761_);
return v___x_793_;
}
else
{
lean_object* v___x_794_; lean_object* v___y_796_; lean_object* v___y_797_; lean_object* v___y_798_; lean_object* v___y_799_; lean_object* v___y_800_; lean_object* v___y_801_; lean_object* v___y_802_; lean_object* v___y_803_; lean_object* v___y_804_; lean_object* v___y_805_; lean_object* v___y_806_; lean_object* v___y_807_; lean_object* v___y_833_; lean_object* v___y_834_; lean_object* v_phase_x3f_835_; lean_object* v___y_836_; lean_object* v___y_837_; lean_object* v_doc_x3f_859_; lean_object* v___y_860_; lean_object* v___y_861_; lean_object* v___x_877_; uint8_t v___x_878_; 
v___x_794_ = lean_unsigned_to_nat(0u);
v___x_877_ = l_Lean_Syntax_getArg(v_x_759_, v___x_794_);
v___x_878_ = l_Lean_Syntax_isNone(v___x_877_);
if (v___x_878_ == 0)
{
lean_object* v___x_879_; uint8_t v___x_880_; 
v___x_879_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_877_);
v___x_880_ = l_Lean_Syntax_matchesNull(v___x_877_, v___x_879_);
if (v___x_880_ == 0)
{
lean_object* v___x_881_; lean_object* v___x_882_; 
lean_dec(v___x_877_);
lean_dec(v_x_759_);
v___x_881_ = lean_box(1);
v___x_882_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_882_, 0, v___x_881_);
lean_ctor_set(v___x_882_, 1, v_a_761_);
return v___x_882_;
}
else
{
lean_object* v_doc_x3f_883_; lean_object* v___x_884_; uint8_t v___x_885_; 
v_doc_x3f_883_ = l_Lean_Syntax_getArg(v___x_877_, v___x_794_);
lean_dec(v___x_877_);
v___x_884_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__30));
lean_inc(v_doc_x3f_883_);
v___x_885_ = l_Lean_Syntax_isOfKind(v_doc_x3f_883_, v___x_884_);
if (v___x_885_ == 0)
{
lean_object* v___x_886_; lean_object* v___x_887_; 
lean_dec(v_doc_x3f_883_);
lean_dec(v_x_759_);
v___x_886_ = lean_box(1);
v___x_887_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_887_, 0, v___x_886_);
lean_ctor_set(v___x_887_, 1, v_a_761_);
return v___x_887_;
}
else
{
lean_object* v___x_888_; 
v___x_888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_888_, 0, v_doc_x3f_883_);
v_doc_x3f_859_ = v___x_888_;
v___y_860_ = v_a_760_;
v___y_861_ = v_a_761_;
goto v___jp_858_;
}
}
}
else
{
lean_object* v___x_889_; 
lean_dec(v___x_877_);
v___x_889_ = lean_box(0);
v_doc_x3f_859_ = v___x_889_;
v___y_860_ = v_a_760_;
v___y_861_ = v_a_761_;
goto v___jp_858_;
}
v___jp_795_:
{
lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; 
lean_inc_ref(v___y_801_);
v___x_808_ = l_Array_append___redArg(v___y_801_, v___y_807_);
lean_dec_ref(v___y_807_);
lean_inc(v___y_803_);
lean_inc(v___y_797_);
v___x_809_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_809_, 0, v___y_797_);
lean_ctor_set(v___x_809_, 1, v___y_803_);
lean_ctor_set(v___x_809_, 2, v___x_808_);
v___x_810_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Builtin__cbv__simproc_________x28___x29_x3a_x3d____1___closed__0));
lean_inc(v___y_797_);
v___x_811_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_811_, 0, v___y_797_);
lean_ctor_set(v___x_811_, 1, v___x_810_);
v___x_812_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__2));
lean_inc(v___y_797_);
v___x_813_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_813_, 0, v___y_797_);
lean_ctor_set(v___x_813_, 1, v___x_812_);
v___x_814_ = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__34));
lean_inc(v___y_797_);
v___x_815_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_815_, 0, v___y_797_);
lean_ctor_set(v___x_815_, 1, v___x_814_);
v___x_816_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__10));
lean_inc(v___y_797_);
v___x_817_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_817_, 0, v___y_797_);
lean_ctor_set(v___x_817_, 1, v___x_816_);
lean_inc(v___y_805_);
lean_inc(v___y_797_);
v___x_818_ = l_Lean_Syntax_node8(v___y_797_, v___y_800_, v___x_809_, v___x_811_, v___y_805_, v___x_813_, v___y_806_, v___x_815_, v___x_817_, v___y_799_);
v___x_819_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__3));
v___x_820_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__4));
lean_inc(v___y_797_);
v___x_821_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_821_, 0, v___y_797_);
lean_ctor_set(v___x_821_, 1, v___x_819_);
v___x_822_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__5));
lean_inc(v___y_797_);
v___x_823_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_823_, 0, v___y_797_);
lean_ctor_set(v___x_823_, 1, v___x_822_);
v___x_824_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__6));
v___x_825_ = l_Lean_Name_mkStr4(v___x_788_, v___x_789_, v___y_796_, v___x_824_);
v___x_826_ = ((lean_object*)(l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__1));
v___x_827_ = ((lean_object*)(l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__2));
lean_inc(v___y_797_);
v___x_828_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_828_, 0, v___y_797_);
lean_ctor_set(v___x_828_, 1, v___x_827_);
if (lean_obj_tag(v___y_804_) == 1)
{
lean_object* v_val_829_; lean_object* v___x_830_; 
v_val_829_ = lean_ctor_get(v___y_804_, 0);
lean_inc(v_val_829_);
lean_dec_ref(v___y_804_);
v___x_830_ = l_Array_mkArray1___redArg(v_val_829_);
v___y_763_ = v___y_797_;
v___y_764_ = v___y_798_;
v___y_765_ = v___x_823_;
v___y_766_ = v___y_801_;
v___y_767_ = v___x_825_;
v___y_768_ = v___x_828_;
v___y_769_ = v___y_805_;
v___y_770_ = v___x_820_;
v___y_771_ = v___x_818_;
v___y_772_ = v___y_802_;
v___y_773_ = v___y_803_;
v___y_774_ = v___x_821_;
v___y_775_ = v___x_826_;
v___y_776_ = v___x_830_;
goto v___jp_762_;
}
else
{
lean_object* v___x_831_; 
lean_dec(v___y_804_);
v___x_831_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__29));
v___y_763_ = v___y_797_;
v___y_764_ = v___y_798_;
v___y_765_ = v___x_823_;
v___y_766_ = v___y_801_;
v___y_767_ = v___x_825_;
v___y_768_ = v___x_828_;
v___y_769_ = v___y_805_;
v___y_770_ = v___x_820_;
v___y_771_ = v___x_818_;
v___y_772_ = v___y_802_;
v___y_773_ = v___y_803_;
v___y_774_ = v___x_821_;
v___y_775_ = v___x_826_;
v___y_776_ = v___x_831_;
goto v___jp_762_;
}
}
v___jp_832_:
{
lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; uint8_t v___x_841_; 
v___x_838_ = lean_unsigned_to_nat(4u);
v___x_839_ = l_Lean_Syntax_getArg(v_x_759_, v___x_838_);
v___x_840_ = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__24));
lean_inc(v___x_839_);
v___x_841_ = l_Lean_Syntax_isOfKind(v___x_839_, v___x_840_);
if (v___x_841_ == 0)
{
lean_object* v___x_842_; lean_object* v___x_843_; 
lean_dec(v___x_839_);
lean_dec(v_phase_x3f_835_);
lean_dec(v___y_834_);
lean_dec(v___y_833_);
lean_dec(v_x_759_);
v___x_842_ = lean_box(1);
v___x_843_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_843_, 0, v___x_842_);
lean_ctor_set(v___x_843_, 1, v___y_837_);
return v___x_843_;
}
else
{
lean_object* v_ref_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; uint8_t v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
v_ref_844_ = lean_ctor_get(v___y_836_, 5);
v___x_845_ = lean_unsigned_to_nat(6u);
v___x_846_ = l_Lean_Syntax_getArg(v_x_759_, v___x_845_);
v___x_847_ = lean_unsigned_to_nat(9u);
v___x_848_ = l_Lean_Syntax_getArg(v_x_759_, v___x_847_);
lean_dec(v_x_759_);
v___x_849_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__5));
v___x_850_ = 0;
v___x_851_ = l_Lean_SourceInfo_fromRef(v_ref_844_, v___x_850_);
v___x_852_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__22));
v___x_853_ = ((lean_object*)(l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__1));
v___x_854_ = lean_obj_once(&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__28, &l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__28_once, _init_l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__28);
if (lean_obj_tag(v___y_833_) == 1)
{
lean_object* v_val_855_; lean_object* v___x_856_; 
v_val_855_ = lean_ctor_get(v___y_833_, 0);
lean_inc(v_val_855_);
lean_dec_ref(v___y_833_);
v___x_856_ = l_Array_mkArray1___redArg(v_val_855_);
v___y_796_ = v___x_849_;
v___y_797_ = v___x_851_;
v___y_798_ = v___y_834_;
v___y_799_ = v___x_848_;
v___y_800_ = v___x_853_;
v___y_801_ = v___x_854_;
v___y_802_ = v___y_837_;
v___y_803_ = v___x_852_;
v___y_804_ = v_phase_x3f_835_;
v___y_805_ = v___x_839_;
v___y_806_ = v___x_846_;
v___y_807_ = v___x_856_;
goto v___jp_795_;
}
else
{
lean_object* v___x_857_; 
lean_dec(v___y_833_);
v___x_857_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__29));
v___y_796_ = v___x_849_;
v___y_797_ = v___x_851_;
v___y_798_ = v___y_834_;
v___y_799_ = v___x_848_;
v___y_800_ = v___x_853_;
v___y_801_ = v___x_854_;
v___y_802_ = v___y_837_;
v___y_803_ = v___x_852_;
v___y_804_ = v_phase_x3f_835_;
v___y_805_ = v___x_839_;
v___y_806_ = v___x_846_;
v___y_807_ = v___x_857_;
goto v___jp_795_;
}
}
}
v___jp_858_:
{
lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; uint8_t v___x_865_; 
v___x_862_ = lean_unsigned_to_nat(1u);
v___x_863_ = l_Lean_Syntax_getArg(v_x_759_, v___x_862_);
v___x_864_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__7));
lean_inc(v___x_863_);
v___x_865_ = l_Lean_Syntax_isOfKind(v___x_863_, v___x_864_);
if (v___x_865_ == 0)
{
lean_object* v___x_866_; lean_object* v___x_867_; 
lean_dec(v___x_863_);
lean_dec(v_doc_x3f_859_);
lean_dec(v_x_759_);
v___x_866_ = lean_box(1);
v___x_867_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_867_, 0, v___x_866_);
lean_ctor_set(v___x_867_, 1, v___y_861_);
return v___x_867_;
}
else
{
lean_object* v___x_868_; lean_object* v___x_869_; uint8_t v___x_870_; 
v___x_868_ = lean_unsigned_to_nat(3u);
v___x_869_ = l_Lean_Syntax_getArg(v_x_759_, v___x_868_);
v___x_870_ = l_Lean_Syntax_isNone(v___x_869_);
if (v___x_870_ == 0)
{
uint8_t v___x_871_; 
lean_inc(v___x_869_);
v___x_871_ = l_Lean_Syntax_matchesNull(v___x_869_, v___x_862_);
if (v___x_871_ == 0)
{
lean_object* v___x_872_; lean_object* v___x_873_; 
lean_dec(v___x_869_);
lean_dec(v___x_863_);
lean_dec(v_doc_x3f_859_);
lean_dec(v_x_759_);
v___x_872_ = lean_box(1);
v___x_873_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_873_, 0, v___x_872_);
lean_ctor_set(v___x_873_, 1, v___y_861_);
return v___x_873_;
}
else
{
lean_object* v_phase_x3f_874_; lean_object* v___x_875_; 
v_phase_x3f_874_ = l_Lean_Syntax_getArg(v___x_869_, v___x_794_);
lean_dec(v___x_869_);
v___x_875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_875_, 0, v_phase_x3f_874_);
v___y_833_ = v_doc_x3f_859_;
v___y_834_ = v___x_863_;
v_phase_x3f_835_ = v___x_875_;
v___y_836_ = v___y_860_;
v___y_837_ = v___y_861_;
goto v___jp_832_;
}
}
else
{
lean_object* v___x_876_; 
lean_dec(v___x_869_);
v___x_876_ = lean_box(0);
v___y_833_ = v_doc_x3f_859_;
v___y_834_ = v___x_863_;
v_phase_x3f_835_ = v___x_876_;
v___y_836_ = v___y_860_;
v___y_837_ = v___y_861_;
goto v___jp_832_;
}
}
}
}
v___jp_762_:
{
lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_777_ = l_Array_append___redArg(v___y_766_, v___y_776_);
lean_dec_ref(v___y_776_);
lean_inc(v___y_773_);
lean_inc(v___y_763_);
v___x_778_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_778_, 0, v___y_763_);
lean_ctor_set(v___x_778_, 1, v___y_773_);
lean_ctor_set(v___x_778_, 2, v___x_777_);
lean_inc(v___y_763_);
v___x_779_ = l_Lean_Syntax_node2(v___y_763_, v___y_775_, v___y_768_, v___x_778_);
lean_inc(v___y_763_);
v___x_780_ = l_Lean_Syntax_node2(v___y_763_, v___y_767_, v___y_764_, v___x_779_);
lean_inc(v___y_773_);
lean_inc(v___y_763_);
v___x_781_ = l_Lean_Syntax_node1(v___y_763_, v___y_773_, v___x_780_);
v___x_782_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__0));
lean_inc(v___y_763_);
v___x_783_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_783_, 0, v___y_763_);
lean_ctor_set(v___x_783_, 1, v___x_782_);
lean_inc(v___y_773_);
lean_inc(v___y_763_);
v___x_784_ = l_Lean_Syntax_node1(v___y_763_, v___y_773_, v___y_769_);
lean_inc(v___y_763_);
v___x_785_ = l_Lean_Syntax_node5(v___y_763_, v___y_770_, v___y_774_, v___y_765_, v___x_781_, v___x_783_, v___x_784_);
v___x_786_ = l_Lean_Syntax_node2(v___y_763_, v___y_773_, v___y_771_, v___x_785_);
v___x_787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_787_, 0, v___x_786_);
lean_ctor_set(v___x_787_, 1, v___y_772_);
return v___x_787_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Builtin__cbv__simproc_________x28___x29_x3a_x3d____1___boxed(lean_object* v_x_890_, lean_object* v_a_891_, lean_object* v_a_892_){
_start:
{
lean_object* v_res_893_; 
v_res_893_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Builtin__cbv__simproc_________x28___x29_x3a_x3d____1(v_x_890_, v_a_891_, v_a_892_);
lean_dec_ref(v_a_891_);
return v_res_893_;
}
}
lean_object* runtime_initialize_Init_Tactics(uint8_t builtin);
lean_object* runtime_initialize_Init_Meta_Defs(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_CbvSimproc(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Meta_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Init_Data_ToString_Name(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_CbvSimproc(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Init_Data_ToString_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d__ = _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d__();
lean_mark_persistent(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d__);
l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d__ = _init_l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d__();
lean_mark_persistent(l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d__);
l_Lean_Parser_Attr_cbvSimprocAttr = _init_l_Lean_Parser_Attr_cbvSimprocAttr();
lean_mark_persistent(l_Lean_Parser_Attr_cbvSimprocAttr);
l_Lean_Parser_Attr_cbvSimprocBuiltinAttr = _init_l_Lean_Parser_Attr_cbvSimprocBuiltinAttr();
lean_mark_persistent(l_Lean_Parser_Attr_cbvSimprocBuiltinAttr);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_ToString_Name(uint8_t builtin);
lean_object* initialize_Init_Tactics(uint8_t builtin);
lean_object* initialize_Init_Meta_Defs(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_CbvSimproc(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_ToString_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Meta_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_CbvSimproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_CbvSimproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_CbvSimproc(builtin);
}
#ifdef __cplusplus
}
#endif

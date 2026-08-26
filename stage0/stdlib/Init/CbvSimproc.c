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
lean_object* l_Lean_mkIdent(lean_object*);
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
lean_object* v_doc_x3f_492_; 
v_doc_x3f_492_ = l_Lean_Syntax_getArg(v___x_486_, v___x_485_);
lean_dec(v___x_486_);
if (v___x_487_ == 0)
{
lean_object* v___x_495_; uint8_t v___x_496_; 
v___x_495_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__30));
lean_inc(v_doc_x3f_492_);
v___x_496_ = l_Lean_Syntax_isOfKind(v_doc_x3f_492_, v___x_495_);
if (v___x_496_ == 0)
{
lean_object* v___x_497_; lean_object* v___x_498_; 
lean_dec(v_doc_x3f_492_);
lean_dec(v_x_395_);
v___x_497_ = lean_box(1);
v___x_498_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_498_, 0, v___x_497_);
lean_ctor_set(v___x_498_, 1, v_a_397_);
return v___x_498_;
}
else
{
goto v___jp_493_;
}
}
else
{
goto v___jp_493_;
}
v___jp_493_:
{
lean_object* v___x_494_; 
v___x_494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_494_, 0, v_doc_x3f_492_);
v_doc_x3f_456_ = v___x_494_;
v___y_457_ = v_a_396_;
v___y_458_ = v_a_397_;
goto v___jp_455_;
}
}
}
else
{
lean_object* v___x_499_; 
lean_dec(v___x_486_);
v___x_499_ = lean_box(0);
v_doc_x3f_456_ = v___x_499_;
v___y_457_ = v_a_396_;
v___y_458_ = v_a_397_;
goto v___jp_455_;
}
}
v___jp_400_:
{
lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
lean_inc_ref_n(v___y_408_, 2);
v___x_413_ = l_Array_append___redArg(v___y_408_, v___y_412_);
lean_dec_ref(v___y_412_);
lean_inc_n(v___y_402_, 5);
lean_inc_n(v___y_409_, 20);
v___x_414_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_414_, 0, v___y_409_);
lean_ctor_set(v___x_414_, 1, v___y_402_);
lean_ctor_set(v___x_414_, 2, v___x_413_);
v___x_415_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_415_, 0, v___y_409_);
lean_ctor_set(v___x_415_, 1, v___y_402_);
lean_ctor_set(v___x_415_, 2, v___y_408_);
v___x_416_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__0));
lean_inc_ref_n(v___y_411_, 5);
v___x_417_ = l_Lean_Name_mkStr4(v___x_398_, v___x_399_, v___y_411_, v___x_416_);
v___x_418_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_418_, 0, v___y_409_);
lean_ctor_set(v___x_418_, 1, v___x_416_);
v___x_419_ = l_Lean_Syntax_node1(v___y_409_, v___x_417_, v___x_418_);
v___x_420_ = l_Lean_Syntax_node1(v___y_409_, v___y_402_, v___x_419_);
lean_inc_ref_n(v___x_415_, 10);
lean_inc(v___y_403_);
v___x_421_ = l_Lean_Syntax_node7(v___y_409_, v___y_403_, v___x_414_, v___x_415_, v___x_415_, v___x_415_, v___x_420_, v___x_415_, v___x_415_);
v___x_422_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__1));
v___x_423_ = l_Lean_Name_mkStr4(v___x_398_, v___x_399_, v___y_411_, v___x_422_);
v___x_424_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__2));
v___x_425_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_425_, 0, v___y_409_);
lean_ctor_set(v___x_425_, 1, v___x_424_);
v___x_426_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__3));
v___x_427_ = l_Lean_Name_mkStr4(v___x_398_, v___x_399_, v___y_411_, v___x_426_);
lean_inc(v___y_404_);
v___x_428_ = l_Lean_Syntax_node2(v___y_409_, v___x_427_, v___y_404_, v___x_415_);
v___x_429_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__4));
v___x_430_ = l_Lean_Name_mkStr4(v___x_398_, v___x_399_, v___y_411_, v___x_429_);
v___x_431_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__7));
v___x_432_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__8));
v___x_433_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_433_, 0, v___y_409_);
lean_ctor_set(v___x_433_, 1, v___x_432_);
lean_inc(v___y_407_);
v___x_434_ = l_Lean_mkIdent(v___y_407_);
v___x_435_ = l_Lean_Syntax_node2(v___y_409_, v___x_431_, v___x_433_, v___x_434_);
v___x_436_ = l_Lean_Syntax_node1(v___y_409_, v___y_402_, v___x_435_);
v___x_437_ = l_Lean_Syntax_node2(v___y_409_, v___x_430_, v___x_415_, v___x_436_);
v___x_438_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__9));
v___x_439_ = l_Lean_Name_mkStr4(v___x_398_, v___x_399_, v___y_411_, v___x_438_);
v___x_440_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__10));
v___x_441_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_441_, 0, v___y_409_);
lean_ctor_set(v___x_441_, 1, v___x_440_);
v___x_442_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__13));
v___x_443_ = l_Lean_Syntax_node2(v___y_409_, v___x_442_, v___x_415_, v___x_415_);
v___x_444_ = l_Lean_Syntax_node4(v___y_409_, v___x_439_, v___x_441_, v___y_405_, v___x_443_, v___x_415_);
v___x_445_ = l_Lean_Syntax_node5(v___y_409_, v___x_423_, v___x_425_, v___x_428_, v___x_437_, v___x_444_, v___x_415_);
lean_inc(v___y_401_);
v___x_446_ = l_Lean_Syntax_node2(v___y_409_, v___y_401_, v___x_421_, v___x_445_);
v___x_447_ = ((lean_object*)(l_Lean_Parser_cbvSimprocPattern___closed__1));
v___x_448_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__14));
v___x_449_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_449_, 0, v___y_409_);
lean_ctor_set(v___x_449_, 1, v___x_448_);
v___x_450_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__15));
v___x_451_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_451_, 0, v___y_409_);
lean_ctor_set(v___x_451_, 1, v___x_450_);
v___x_452_ = l_Lean_Syntax_node4(v___y_409_, v___x_447_, v___x_449_, v___y_410_, v___x_451_, v___y_404_);
v___x_453_ = l_Lean_Syntax_node2(v___y_409_, v___y_402_, v___x_446_, v___x_452_);
v___x_454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_454_, 0, v___x_453_);
lean_ctor_set(v___x_454_, 1, v___y_406_);
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
lean_dec_ref_known(v_doc_x3f_456_, 1);
v___x_479_ = l_Array_mkArray1___redArg(v_val_478_);
v___y_401_ = v___x_475_;
v___y_402_ = v___x_473_;
v___y_403_ = v___x_476_;
v___y_404_ = v___x_460_;
v___y_405_ = v___x_469_;
v___y_406_ = v___y_458_;
v___y_407_ = v_simprocType_470_;
v___y_408_ = v___x_477_;
v___y_409_ = v___x_472_;
v___y_410_ = v___x_467_;
v___y_411_ = v___x_474_;
v___y_412_ = v___x_479_;
goto v___jp_400_;
}
else
{
lean_object* v___x_480_; 
lean_dec(v_doc_x3f_456_);
v___x_480_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__29));
v___y_401_ = v___x_475_;
v___y_402_ = v___x_473_;
v___y_403_ = v___x_476_;
v___y_404_ = v___x_460_;
v___y_405_ = v___x_469_;
v___y_406_ = v___y_458_;
v___y_407_ = v_simprocType_470_;
v___y_408_ = v___x_477_;
v___y_409_ = v___x_472_;
v___y_410_ = v___x_467_;
v___y_411_ = v___x_474_;
v___y_412_ = v___x_480_;
goto v___jp_400_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___boxed(lean_object* v_x_500_, lean_object* v_a_501_, lean_object* v_a_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1(v_x_500_, v_a_501_, v_a_502_);
lean_dec_ref(v_a_501_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d____1(lean_object* v_x_505_, lean_object* v_a_506_, lean_object* v_a_507_){
_start:
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___y_511_; lean_object* v___y_512_; lean_object* v___y_513_; lean_object* v___y_514_; lean_object* v___y_515_; lean_object* v___y_516_; lean_object* v___y_517_; lean_object* v___y_518_; lean_object* v___y_519_; lean_object* v___y_520_; lean_object* v___y_521_; lean_object* v___y_522_; lean_object* v_doc_x3f_561_; lean_object* v___y_562_; lean_object* v___y_563_; lean_object* v___x_586_; uint8_t v___x_587_; 
v___x_508_ = ((lean_object*)(l_Lean_Parser_cbvSimprocEval___closed__1));
v___x_509_ = ((lean_object*)(l_Lean_Parser_cbvSimprocEval___closed__2));
v___x_586_ = ((lean_object*)(l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__1));
lean_inc(v_x_505_);
v___x_587_ = l_Lean_Syntax_isOfKind(v_x_505_, v___x_586_);
if (v___x_587_ == 0)
{
lean_object* v___x_588_; lean_object* v___x_589_; 
lean_dec(v_x_505_);
v___x_588_ = lean_box(1);
v___x_589_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_589_, 0, v___x_588_);
lean_ctor_set(v___x_589_, 1, v_a_507_);
return v___x_589_;
}
else
{
lean_object* v___x_590_; lean_object* v___x_591_; uint8_t v___x_592_; 
v___x_590_ = lean_unsigned_to_nat(0u);
v___x_591_ = l_Lean_Syntax_getArg(v_x_505_, v___x_590_);
v___x_592_ = l_Lean_Syntax_isNone(v___x_591_);
if (v___x_592_ == 0)
{
lean_object* v___x_593_; uint8_t v___x_594_; 
v___x_593_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_591_);
v___x_594_ = l_Lean_Syntax_matchesNull(v___x_591_, v___x_593_);
if (v___x_594_ == 0)
{
lean_object* v___x_595_; lean_object* v___x_596_; 
lean_dec(v___x_591_);
lean_dec(v_x_505_);
v___x_595_ = lean_box(1);
v___x_596_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_596_, 0, v___x_595_);
lean_ctor_set(v___x_596_, 1, v_a_507_);
return v___x_596_;
}
else
{
lean_object* v_doc_x3f_597_; 
v_doc_x3f_597_ = l_Lean_Syntax_getArg(v___x_591_, v___x_590_);
lean_dec(v___x_591_);
if (v___x_592_ == 0)
{
lean_object* v___x_600_; uint8_t v___x_601_; 
v___x_600_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__30));
lean_inc(v_doc_x3f_597_);
v___x_601_ = l_Lean_Syntax_isOfKind(v_doc_x3f_597_, v___x_600_);
if (v___x_601_ == 0)
{
lean_object* v___x_602_; lean_object* v___x_603_; 
lean_dec(v_doc_x3f_597_);
lean_dec(v_x_505_);
v___x_602_ = lean_box(1);
v___x_603_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_603_, 0, v___x_602_);
lean_ctor_set(v___x_603_, 1, v_a_507_);
return v___x_603_;
}
else
{
goto v___jp_598_;
}
}
else
{
goto v___jp_598_;
}
v___jp_598_:
{
lean_object* v___x_599_; 
v___x_599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_599_, 0, v_doc_x3f_597_);
v_doc_x3f_561_ = v___x_599_;
v___y_562_ = v_a_506_;
v___y_563_ = v_a_507_;
goto v___jp_560_;
}
}
}
else
{
lean_object* v___x_604_; 
lean_dec(v___x_591_);
v___x_604_ = lean_box(0);
v_doc_x3f_561_ = v___x_604_;
v___y_562_ = v_a_506_;
v___y_563_ = v_a_507_;
goto v___jp_560_;
}
}
v___jp_510_:
{
lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
lean_inc_ref_n(v___y_521_, 2);
v___x_523_ = l_Array_append___redArg(v___y_521_, v___y_522_);
lean_dec_ref(v___y_522_);
lean_inc_n(v___y_514_, 4);
lean_inc_n(v___y_519_, 17);
v___x_524_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_524_, 0, v___y_519_);
lean_ctor_set(v___x_524_, 1, v___y_514_);
lean_ctor_set(v___x_524_, 2, v___x_523_);
v___x_525_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_525_, 0, v___y_519_);
lean_ctor_set(v___x_525_, 1, v___y_514_);
lean_ctor_set(v___x_525_, 2, v___y_521_);
lean_inc_ref_n(v___x_525_, 11);
lean_inc(v___y_520_);
v___x_526_ = l_Lean_Syntax_node7(v___y_519_, v___y_520_, v___x_524_, v___x_525_, v___x_525_, v___x_525_, v___x_525_, v___x_525_, v___x_525_);
v___x_527_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__1));
lean_inc_ref_n(v___y_518_, 4);
v___x_528_ = l_Lean_Name_mkStr4(v___x_508_, v___x_509_, v___y_518_, v___x_527_);
v___x_529_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__2));
v___x_530_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_530_, 0, v___y_519_);
lean_ctor_set(v___x_530_, 1, v___x_529_);
v___x_531_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__3));
v___x_532_ = l_Lean_Name_mkStr4(v___x_508_, v___x_509_, v___y_518_, v___x_531_);
lean_inc(v___y_517_);
v___x_533_ = l_Lean_Syntax_node2(v___y_519_, v___x_532_, v___y_517_, v___x_525_);
v___x_534_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__4));
v___x_535_ = l_Lean_Name_mkStr4(v___x_508_, v___x_509_, v___y_518_, v___x_534_);
v___x_536_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__7));
v___x_537_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__8));
v___x_538_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_538_, 0, v___y_519_);
lean_ctor_set(v___x_538_, 1, v___x_537_);
lean_inc(v___y_512_);
v___x_539_ = l_Lean_mkIdent(v___y_512_);
v___x_540_ = l_Lean_Syntax_node2(v___y_519_, v___x_536_, v___x_538_, v___x_539_);
v___x_541_ = l_Lean_Syntax_node1(v___y_519_, v___y_514_, v___x_540_);
v___x_542_ = l_Lean_Syntax_node2(v___y_519_, v___x_535_, v___x_525_, v___x_541_);
v___x_543_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__9));
v___x_544_ = l_Lean_Name_mkStr4(v___x_508_, v___x_509_, v___y_518_, v___x_543_);
v___x_545_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__10));
v___x_546_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_546_, 0, v___y_519_);
lean_ctor_set(v___x_546_, 1, v___x_545_);
v___x_547_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__13));
v___x_548_ = l_Lean_Syntax_node2(v___y_519_, v___x_547_, v___x_525_, v___x_525_);
v___x_549_ = l_Lean_Syntax_node4(v___y_519_, v___x_544_, v___x_546_, v___y_516_, v___x_548_, v___x_525_);
v___x_550_ = l_Lean_Syntax_node5(v___y_519_, v___x_528_, v___x_530_, v___x_533_, v___x_542_, v___x_549_, v___x_525_);
lean_inc(v___y_511_);
v___x_551_ = l_Lean_Syntax_node2(v___y_519_, v___y_511_, v___x_526_, v___x_550_);
v___x_552_ = ((lean_object*)(l_Lean_Parser_cbvSimprocPatternBuiltin___closed__1));
v___x_553_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__0));
v___x_554_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_554_, 0, v___y_519_);
lean_ctor_set(v___x_554_, 1, v___x_553_);
v___x_555_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__15));
v___x_556_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_556_, 0, v___y_519_);
lean_ctor_set(v___x_556_, 1, v___x_555_);
v___x_557_ = l_Lean_Syntax_node4(v___y_519_, v___x_552_, v___x_554_, v___y_513_, v___x_556_, v___y_517_);
v___x_558_ = l_Lean_Syntax_node2(v___y_519_, v___y_514_, v___x_551_, v___x_557_);
v___x_559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_559_, 0, v___x_558_);
lean_ctor_set(v___x_559_, 1, v___y_515_);
return v___x_559_;
}
v___jp_560_:
{
lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; uint8_t v___x_567_; 
v___x_564_ = lean_unsigned_to_nat(2u);
v___x_565_ = l_Lean_Syntax_getArg(v_x_505_, v___x_564_);
v___x_566_ = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__24));
lean_inc(v___x_565_);
v___x_567_ = l_Lean_Syntax_isOfKind(v___x_565_, v___x_566_);
if (v___x_567_ == 0)
{
lean_object* v___x_568_; lean_object* v___x_569_; 
lean_dec(v___x_565_);
lean_dec(v_doc_x3f_561_);
lean_dec(v_x_505_);
v___x_568_ = lean_box(1);
v___x_569_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_569_, 0, v___x_568_);
lean_ctor_set(v___x_569_, 1, v___y_563_);
return v___x_569_;
}
else
{
lean_object* v_ref_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v_simprocType_575_; uint8_t v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v_ref_570_ = lean_ctor_get(v___y_562_, 5);
v___x_571_ = lean_unsigned_to_nat(4u);
v___x_572_ = l_Lean_Syntax_getArg(v_x_505_, v___x_571_);
v___x_573_ = lean_unsigned_to_nat(7u);
v___x_574_ = l_Lean_Syntax_getArg(v_x_505_, v___x_573_);
lean_dec(v_x_505_);
v_simprocType_575_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__20));
v___x_576_ = 0;
v___x_577_ = l_Lean_SourceInfo_fromRef(v_ref_570_, v___x_576_);
v___x_578_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__22));
v___x_579_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__23));
v___x_580_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__25));
v___x_581_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__27));
v___x_582_ = lean_obj_once(&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__28, &l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__28_once, _init_l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__28);
if (lean_obj_tag(v_doc_x3f_561_) == 1)
{
lean_object* v_val_583_; lean_object* v___x_584_; 
v_val_583_ = lean_ctor_get(v_doc_x3f_561_, 0);
lean_inc(v_val_583_);
lean_dec_ref_known(v_doc_x3f_561_, 1);
v___x_584_ = l_Array_mkArray1___redArg(v_val_583_);
v___y_511_ = v___x_580_;
v___y_512_ = v_simprocType_575_;
v___y_513_ = v___x_572_;
v___y_514_ = v___x_578_;
v___y_515_ = v___y_563_;
v___y_516_ = v___x_574_;
v___y_517_ = v___x_565_;
v___y_518_ = v___x_579_;
v___y_519_ = v___x_577_;
v___y_520_ = v___x_581_;
v___y_521_ = v___x_582_;
v___y_522_ = v___x_584_;
goto v___jp_510_;
}
else
{
lean_object* v___x_585_; 
lean_dec(v_doc_x3f_561_);
v___x_585_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__29));
v___y_511_ = v___x_580_;
v___y_512_ = v_simprocType_575_;
v___y_513_ = v___x_572_;
v___y_514_ = v___x_578_;
v___y_515_ = v___y_563_;
v___y_516_ = v___x_574_;
v___y_517_ = v___x_565_;
v___y_518_ = v___x_579_;
v___y_519_ = v___x_577_;
v___y_520_ = v___x_581_;
v___y_521_ = v___x_582_;
v___y_522_ = v___x_585_;
goto v___jp_510_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d____1___boxed(lean_object* v_x_605_, lean_object* v_a_606_, lean_object* v_a_607_){
_start:
{
lean_object* v_res_608_; 
v_res_608_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d____1(v_x_605_, v_a_606_, v_a_607_);
lean_dec_ref(v_a_606_);
return v_res_608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1(lean_object* v_x_625_, lean_object* v_a_626_, lean_object* v_a_627_){
_start:
{
lean_object* v___y_629_; lean_object* v___y_630_; lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; uint8_t v___x_657_; 
v___x_654_ = ((lean_object*)(l_Lean_Parser_cbvSimprocEval___closed__1));
v___x_655_ = ((lean_object*)(l_Lean_Parser_cbvSimprocEval___closed__2));
v___x_656_ = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__1));
lean_inc(v_x_625_);
v___x_657_ = l_Lean_Syntax_isOfKind(v_x_625_, v___x_656_);
if (v___x_657_ == 0)
{
lean_object* v___x_658_; lean_object* v___x_659_; 
lean_dec(v_x_625_);
v___x_658_ = lean_box(1);
v___x_659_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_659_, 0, v___x_658_);
lean_ctor_set(v___x_659_, 1, v_a_627_);
return v___x_659_;
}
else
{
lean_object* v___x_660_; lean_object* v___y_662_; lean_object* v___y_663_; lean_object* v___y_664_; lean_object* v___y_665_; lean_object* v___y_666_; lean_object* v___y_667_; lean_object* v___y_668_; lean_object* v___y_669_; lean_object* v___y_670_; lean_object* v___y_671_; lean_object* v___y_672_; lean_object* v___y_673_; lean_object* v___y_699_; lean_object* v___y_700_; lean_object* v_phase_x3f_701_; lean_object* v___y_702_; lean_object* v___y_703_; lean_object* v_doc_x3f_725_; lean_object* v___y_726_; lean_object* v___y_727_; lean_object* v___x_743_; uint8_t v___x_744_; 
v___x_660_ = lean_unsigned_to_nat(0u);
v___x_743_ = l_Lean_Syntax_getArg(v_x_625_, v___x_660_);
v___x_744_ = l_Lean_Syntax_isNone(v___x_743_);
if (v___x_744_ == 0)
{
lean_object* v___x_745_; uint8_t v___x_746_; 
v___x_745_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_743_);
v___x_746_ = l_Lean_Syntax_matchesNull(v___x_743_, v___x_745_);
if (v___x_746_ == 0)
{
lean_object* v___x_747_; lean_object* v___x_748_; 
lean_dec(v___x_743_);
lean_dec(v_x_625_);
v___x_747_ = lean_box(1);
v___x_748_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_748_, 0, v___x_747_);
lean_ctor_set(v___x_748_, 1, v_a_627_);
return v___x_748_;
}
else
{
lean_object* v_doc_x3f_749_; 
v_doc_x3f_749_ = l_Lean_Syntax_getArg(v___x_743_, v___x_660_);
lean_dec(v___x_743_);
if (v___x_744_ == 0)
{
lean_object* v___x_752_; uint8_t v___x_753_; 
v___x_752_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__30));
lean_inc(v_doc_x3f_749_);
v___x_753_ = l_Lean_Syntax_isOfKind(v_doc_x3f_749_, v___x_752_);
if (v___x_753_ == 0)
{
lean_object* v___x_754_; lean_object* v___x_755_; 
lean_dec(v_doc_x3f_749_);
lean_dec(v_x_625_);
v___x_754_ = lean_box(1);
v___x_755_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_755_, 0, v___x_754_);
lean_ctor_set(v___x_755_, 1, v_a_627_);
return v___x_755_;
}
else
{
goto v___jp_750_;
}
}
else
{
goto v___jp_750_;
}
v___jp_750_:
{
lean_object* v___x_751_; 
v___x_751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_751_, 0, v_doc_x3f_749_);
v_doc_x3f_725_ = v___x_751_;
v___y_726_ = v_a_626_;
v___y_727_ = v_a_627_;
goto v___jp_724_;
}
}
}
else
{
lean_object* v___x_756_; 
lean_dec(v___x_743_);
v___x_756_ = lean_box(0);
v_doc_x3f_725_ = v___x_756_;
v___y_726_ = v_a_626_;
v___y_727_ = v_a_627_;
goto v___jp_724_;
}
v___jp_661_:
{
lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; 
lean_inc_ref(v___y_670_);
v___x_674_ = l_Array_append___redArg(v___y_670_, v___y_673_);
lean_dec_ref(v___y_673_);
lean_inc(v___y_662_);
lean_inc_n(v___y_672_, 9);
v___x_675_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_675_, 0, v___y_672_);
lean_ctor_set(v___x_675_, 1, v___y_662_);
lean_ctor_set(v___x_675_, 2, v___x_674_);
v___x_676_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__1));
v___x_677_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_677_, 0, v___y_672_);
lean_ctor_set(v___x_677_, 1, v___x_676_);
v___x_678_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__2));
v___x_679_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_679_, 0, v___y_672_);
lean_ctor_set(v___x_679_, 1, v___x_678_);
v___x_680_ = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__34));
v___x_681_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_681_, 0, v___y_672_);
lean_ctor_set(v___x_681_, 1, v___x_680_);
v___x_682_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__10));
v___x_683_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_683_, 0, v___y_672_);
lean_ctor_set(v___x_683_, 1, v___x_682_);
lean_inc(v___y_669_);
lean_inc(v___y_665_);
v___x_684_ = l_Lean_Syntax_node8(v___y_672_, v___y_665_, v___x_675_, v___x_677_, v___y_669_, v___x_679_, v___y_667_, v___x_681_, v___x_683_, v___y_668_);
v___x_685_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__3));
v___x_686_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__4));
v___x_687_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_687_, 0, v___y_672_);
lean_ctor_set(v___x_687_, 1, v___x_685_);
v___x_688_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__5));
v___x_689_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_689_, 0, v___y_672_);
lean_ctor_set(v___x_689_, 1, v___x_688_);
v___x_690_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__6));
lean_inc_ref(v___y_666_);
v___x_691_ = l_Lean_Name_mkStr4(v___x_654_, v___x_655_, v___y_666_, v___x_690_);
v___x_692_ = ((lean_object*)(l_Lean_Parser_Attr_cbvSimprocAttr___closed__2));
v___x_693_ = ((lean_object*)(l_Lean_Parser_Attr_cbvSimprocAttr___closed__3));
v___x_694_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_694_, 0, v___y_672_);
lean_ctor_set(v___x_694_, 1, v___x_693_);
if (lean_obj_tag(v___y_663_) == 1)
{
lean_object* v_val_695_; lean_object* v___x_696_; 
v_val_695_ = lean_ctor_get(v___y_663_, 0);
lean_inc(v_val_695_);
lean_dec_ref_known(v___y_663_, 1);
v___x_696_ = l_Array_mkArray1___redArg(v_val_695_);
v___y_629_ = v___y_662_;
v___y_630_ = v___y_664_;
v___y_631_ = v___x_686_;
v___y_632_ = v___y_670_;
v___y_633_ = v___x_694_;
v___y_634_ = v___x_691_;
v___y_635_ = v___y_672_;
v___y_636_ = v___y_671_;
v___y_637_ = v___x_687_;
v___y_638_ = v___y_669_;
v___y_639_ = v___x_692_;
v___y_640_ = v___x_689_;
v___y_641_ = v___x_684_;
v___y_642_ = v___x_696_;
goto v___jp_628_;
}
else
{
lean_object* v___x_697_; 
lean_dec(v___y_663_);
v___x_697_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__29));
v___y_629_ = v___y_662_;
v___y_630_ = v___y_664_;
v___y_631_ = v___x_686_;
v___y_632_ = v___y_670_;
v___y_633_ = v___x_694_;
v___y_634_ = v___x_691_;
v___y_635_ = v___y_672_;
v___y_636_ = v___y_671_;
v___y_637_ = v___x_687_;
v___y_638_ = v___y_669_;
v___y_639_ = v___x_692_;
v___y_640_ = v___x_689_;
v___y_641_ = v___x_684_;
v___y_642_ = v___x_697_;
goto v___jp_628_;
}
}
v___jp_698_:
{
lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; uint8_t v___x_707_; 
v___x_704_ = lean_unsigned_to_nat(4u);
v___x_705_ = l_Lean_Syntax_getArg(v_x_625_, v___x_704_);
v___x_706_ = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__24));
lean_inc(v___x_705_);
v___x_707_ = l_Lean_Syntax_isOfKind(v___x_705_, v___x_706_);
if (v___x_707_ == 0)
{
lean_object* v___x_708_; lean_object* v___x_709_; 
lean_dec(v___x_705_);
lean_dec(v_phase_x3f_701_);
lean_dec(v___y_700_);
lean_dec(v___y_699_);
lean_dec(v_x_625_);
v___x_708_ = lean_box(1);
v___x_709_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_709_, 0, v___x_708_);
lean_ctor_set(v___x_709_, 1, v___y_703_);
return v___x_709_;
}
else
{
lean_object* v_ref_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; uint8_t v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
v_ref_710_ = lean_ctor_get(v___y_702_, 5);
v___x_711_ = lean_unsigned_to_nat(6u);
v___x_712_ = l_Lean_Syntax_getArg(v_x_625_, v___x_711_);
v___x_713_ = lean_unsigned_to_nat(9u);
v___x_714_ = l_Lean_Syntax_getArg(v_x_625_, v___x_713_);
lean_dec(v_x_625_);
v___x_715_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__5));
v___x_716_ = 0;
v___x_717_ = l_Lean_SourceInfo_fromRef(v_ref_710_, v___x_716_);
v___x_718_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__22));
v___x_719_ = ((lean_object*)(l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__1));
v___x_720_ = lean_obj_once(&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__28, &l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__28_once, _init_l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__28);
if (lean_obj_tag(v___y_700_) == 1)
{
lean_object* v_val_721_; lean_object* v___x_722_; 
v_val_721_ = lean_ctor_get(v___y_700_, 0);
lean_inc(v_val_721_);
lean_dec_ref_known(v___y_700_, 1);
v___x_722_ = l_Array_mkArray1___redArg(v_val_721_);
v___y_662_ = v___x_718_;
v___y_663_ = v_phase_x3f_701_;
v___y_664_ = v___y_699_;
v___y_665_ = v___x_719_;
v___y_666_ = v___x_715_;
v___y_667_ = v___x_712_;
v___y_668_ = v___x_714_;
v___y_669_ = v___x_705_;
v___y_670_ = v___x_720_;
v___y_671_ = v___y_703_;
v___y_672_ = v___x_717_;
v___y_673_ = v___x_722_;
goto v___jp_661_;
}
else
{
lean_object* v___x_723_; 
lean_dec(v___y_700_);
v___x_723_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__29));
v___y_662_ = v___x_718_;
v___y_663_ = v_phase_x3f_701_;
v___y_664_ = v___y_699_;
v___y_665_ = v___x_719_;
v___y_666_ = v___x_715_;
v___y_667_ = v___x_712_;
v___y_668_ = v___x_714_;
v___y_669_ = v___x_705_;
v___y_670_ = v___x_720_;
v___y_671_ = v___y_703_;
v___y_672_ = v___x_717_;
v___y_673_ = v___x_723_;
goto v___jp_661_;
}
}
}
v___jp_724_:
{
lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; uint8_t v___x_731_; 
v___x_728_ = lean_unsigned_to_nat(1u);
v___x_729_ = l_Lean_Syntax_getArg(v_x_625_, v___x_728_);
v___x_730_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__7));
lean_inc(v___x_729_);
v___x_731_ = l_Lean_Syntax_isOfKind(v___x_729_, v___x_730_);
if (v___x_731_ == 0)
{
lean_object* v___x_732_; lean_object* v___x_733_; 
lean_dec(v___x_729_);
lean_dec(v_doc_x3f_725_);
lean_dec(v_x_625_);
v___x_732_ = lean_box(1);
v___x_733_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_733_, 0, v___x_732_);
lean_ctor_set(v___x_733_, 1, v___y_727_);
return v___x_733_;
}
else
{
lean_object* v___x_734_; lean_object* v___x_735_; uint8_t v___x_736_; 
v___x_734_ = lean_unsigned_to_nat(3u);
v___x_735_ = l_Lean_Syntax_getArg(v_x_625_, v___x_734_);
v___x_736_ = l_Lean_Syntax_isNone(v___x_735_);
if (v___x_736_ == 0)
{
uint8_t v___x_737_; 
lean_inc(v___x_735_);
v___x_737_ = l_Lean_Syntax_matchesNull(v___x_735_, v___x_728_);
if (v___x_737_ == 0)
{
lean_object* v___x_738_; lean_object* v___x_739_; 
lean_dec(v___x_735_);
lean_dec(v___x_729_);
lean_dec(v_doc_x3f_725_);
lean_dec(v_x_625_);
v___x_738_ = lean_box(1);
v___x_739_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_739_, 0, v___x_738_);
lean_ctor_set(v___x_739_, 1, v___y_727_);
return v___x_739_;
}
else
{
lean_object* v_phase_x3f_740_; lean_object* v___x_741_; 
v_phase_x3f_740_ = l_Lean_Syntax_getArg(v___x_735_, v___x_660_);
lean_dec(v___x_735_);
v___x_741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_741_, 0, v_phase_x3f_740_);
v___y_699_ = v___x_729_;
v___y_700_ = v_doc_x3f_725_;
v_phase_x3f_701_ = v___x_741_;
v___y_702_ = v___y_726_;
v___y_703_ = v___y_727_;
goto v___jp_698_;
}
}
else
{
lean_object* v___x_742_; 
lean_dec(v___x_735_);
v___x_742_ = lean_box(0);
v___y_699_ = v___x_729_;
v___y_700_ = v_doc_x3f_725_;
v_phase_x3f_701_ = v___x_742_;
v___y_702_ = v___y_726_;
v___y_703_ = v___y_727_;
goto v___jp_698_;
}
}
}
}
v___jp_628_:
{
lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
lean_inc_ref(v___y_632_);
v___x_643_ = l_Array_append___redArg(v___y_632_, v___y_642_);
lean_dec_ref(v___y_642_);
lean_inc_n(v___y_629_, 4);
lean_inc_n(v___y_635_, 7);
v___x_644_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_644_, 0, v___y_635_);
lean_ctor_set(v___x_644_, 1, v___y_629_);
lean_ctor_set(v___x_644_, 2, v___x_643_);
lean_inc(v___y_639_);
v___x_645_ = l_Lean_Syntax_node2(v___y_635_, v___y_639_, v___y_633_, v___x_644_);
v___x_646_ = l_Lean_Syntax_node2(v___y_635_, v___y_634_, v___y_630_, v___x_645_);
v___x_647_ = l_Lean_Syntax_node1(v___y_635_, v___y_629_, v___x_646_);
v___x_648_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__0));
v___x_649_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_649_, 0, v___y_635_);
lean_ctor_set(v___x_649_, 1, v___x_648_);
v___x_650_ = l_Lean_Syntax_node1(v___y_635_, v___y_629_, v___y_638_);
lean_inc(v___y_631_);
v___x_651_ = l_Lean_Syntax_node5(v___y_635_, v___y_631_, v___y_637_, v___y_640_, v___x_647_, v___x_649_, v___x_650_);
v___x_652_ = l_Lean_Syntax_node2(v___y_635_, v___y_629_, v___y_641_, v___x_651_);
v___x_653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_653_, 0, v___x_652_);
lean_ctor_set(v___x_653_, 1, v___y_636_);
return v___x_653_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___boxed(lean_object* v_x_757_, lean_object* v_a_758_, lean_object* v_a_759_){
_start:
{
lean_object* v_res_760_; 
v_res_760_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1(v_x_757_, v_a_758_, v_a_759_);
lean_dec_ref(v_a_758_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Builtin__cbv__simproc_________x28___x29_x3a_x3d____1(lean_object* v_x_762_, lean_object* v_a_763_, lean_object* v_a_764_){
_start:
{
lean_object* v___y_766_; lean_object* v___y_767_; lean_object* v___y_768_; lean_object* v___y_769_; lean_object* v___y_770_; lean_object* v___y_771_; lean_object* v___y_772_; lean_object* v___y_773_; lean_object* v___y_774_; lean_object* v___y_775_; lean_object* v___y_776_; lean_object* v___y_777_; lean_object* v___y_778_; lean_object* v___y_779_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; uint8_t v___x_794_; 
v___x_791_ = ((lean_object*)(l_Lean_Parser_cbvSimprocEval___closed__1));
v___x_792_ = ((lean_object*)(l_Lean_Parser_cbvSimprocEval___closed__2));
v___x_793_ = ((lean_object*)(l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__1));
lean_inc(v_x_762_);
v___x_794_ = l_Lean_Syntax_isOfKind(v_x_762_, v___x_793_);
if (v___x_794_ == 0)
{
lean_object* v___x_795_; lean_object* v___x_796_; 
lean_dec(v_x_762_);
v___x_795_ = lean_box(1);
v___x_796_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_796_, 0, v___x_795_);
lean_ctor_set(v___x_796_, 1, v_a_764_);
return v___x_796_;
}
else
{
lean_object* v___x_797_; lean_object* v___y_799_; lean_object* v___y_800_; lean_object* v___y_801_; lean_object* v___y_802_; lean_object* v___y_803_; lean_object* v___y_804_; lean_object* v___y_805_; lean_object* v___y_806_; lean_object* v___y_807_; lean_object* v___y_808_; lean_object* v___y_809_; lean_object* v___y_810_; lean_object* v___y_836_; lean_object* v___y_837_; lean_object* v_phase_x3f_838_; lean_object* v___y_839_; lean_object* v___y_840_; lean_object* v_doc_x3f_862_; lean_object* v___y_863_; lean_object* v___y_864_; lean_object* v___x_880_; uint8_t v___x_881_; 
v___x_797_ = lean_unsigned_to_nat(0u);
v___x_880_ = l_Lean_Syntax_getArg(v_x_762_, v___x_797_);
v___x_881_ = l_Lean_Syntax_isNone(v___x_880_);
if (v___x_881_ == 0)
{
lean_object* v___x_882_; uint8_t v___x_883_; 
v___x_882_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_880_);
v___x_883_ = l_Lean_Syntax_matchesNull(v___x_880_, v___x_882_);
if (v___x_883_ == 0)
{
lean_object* v___x_884_; lean_object* v___x_885_; 
lean_dec(v___x_880_);
lean_dec(v_x_762_);
v___x_884_ = lean_box(1);
v___x_885_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_885_, 0, v___x_884_);
lean_ctor_set(v___x_885_, 1, v_a_764_);
return v___x_885_;
}
else
{
lean_object* v_doc_x3f_886_; 
v_doc_x3f_886_ = l_Lean_Syntax_getArg(v___x_880_, v___x_797_);
lean_dec(v___x_880_);
if (v___x_881_ == 0)
{
lean_object* v___x_889_; uint8_t v___x_890_; 
v___x_889_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__30));
lean_inc(v_doc_x3f_886_);
v___x_890_ = l_Lean_Syntax_isOfKind(v_doc_x3f_886_, v___x_889_);
if (v___x_890_ == 0)
{
lean_object* v___x_891_; lean_object* v___x_892_; 
lean_dec(v_doc_x3f_886_);
lean_dec(v_x_762_);
v___x_891_ = lean_box(1);
v___x_892_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_892_, 0, v___x_891_);
lean_ctor_set(v___x_892_, 1, v_a_764_);
return v___x_892_;
}
else
{
goto v___jp_887_;
}
}
else
{
goto v___jp_887_;
}
v___jp_887_:
{
lean_object* v___x_888_; 
v___x_888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_888_, 0, v_doc_x3f_886_);
v_doc_x3f_862_ = v___x_888_;
v___y_863_ = v_a_763_;
v___y_864_ = v_a_764_;
goto v___jp_861_;
}
}
}
else
{
lean_object* v___x_893_; 
lean_dec(v___x_880_);
v___x_893_ = lean_box(0);
v_doc_x3f_862_ = v___x_893_;
v___y_863_ = v_a_763_;
v___y_864_ = v_a_764_;
goto v___jp_861_;
}
v___jp_798_:
{
lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
lean_inc_ref(v___y_799_);
v___x_811_ = l_Array_append___redArg(v___y_799_, v___y_810_);
lean_dec_ref(v___y_810_);
lean_inc(v___y_809_);
lean_inc_n(v___y_808_, 9);
v___x_812_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_812_, 0, v___y_808_);
lean_ctor_set(v___x_812_, 1, v___y_809_);
lean_ctor_set(v___x_812_, 2, v___x_811_);
v___x_813_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Builtin__cbv__simproc_________x28___x29_x3a_x3d____1___closed__0));
v___x_814_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_814_, 0, v___y_808_);
lean_ctor_set(v___x_814_, 1, v___x_813_);
v___x_815_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__2));
v___x_816_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_816_, 0, v___y_808_);
lean_ctor_set(v___x_816_, 1, v___x_815_);
v___x_817_ = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__34));
v___x_818_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_818_, 0, v___y_808_);
lean_ctor_set(v___x_818_, 1, v___x_817_);
v___x_819_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__10));
v___x_820_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_820_, 0, v___y_808_);
lean_ctor_set(v___x_820_, 1, v___x_819_);
lean_inc(v___y_801_);
lean_inc(v___y_803_);
v___x_821_ = l_Lean_Syntax_node8(v___y_808_, v___y_803_, v___x_812_, v___x_814_, v___y_801_, v___x_816_, v___y_802_, v___x_818_, v___x_820_, v___y_800_);
v___x_822_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__3));
v___x_823_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__4));
v___x_824_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_824_, 0, v___y_808_);
lean_ctor_set(v___x_824_, 1, v___x_822_);
v___x_825_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__5));
v___x_826_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_826_, 0, v___y_808_);
lean_ctor_set(v___x_826_, 1, v___x_825_);
v___x_827_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__6));
lean_inc_ref(v___y_806_);
v___x_828_ = l_Lean_Name_mkStr4(v___x_791_, v___x_792_, v___y_806_, v___x_827_);
v___x_829_ = ((lean_object*)(l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__1));
v___x_830_ = ((lean_object*)(l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__2));
v___x_831_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_831_, 0, v___y_808_);
lean_ctor_set(v___x_831_, 1, v___x_830_);
if (lean_obj_tag(v___y_807_) == 1)
{
lean_object* v_val_832_; lean_object* v___x_833_; 
v_val_832_ = lean_ctor_get(v___y_807_, 0);
lean_inc(v_val_832_);
lean_dec_ref_known(v___y_807_, 1);
v___x_833_ = l_Array_mkArray1___redArg(v_val_832_);
v___y_766_ = v___y_801_;
v___y_767_ = v___x_829_;
v___y_768_ = v___x_824_;
v___y_769_ = v___y_805_;
v___y_770_ = v___x_826_;
v___y_771_ = v___y_799_;
v___y_772_ = v___x_823_;
v___y_773_ = v___x_821_;
v___y_774_ = v___x_831_;
v___y_775_ = v___x_828_;
v___y_776_ = v___y_804_;
v___y_777_ = v___y_808_;
v___y_778_ = v___y_809_;
v___y_779_ = v___x_833_;
goto v___jp_765_;
}
else
{
lean_object* v___x_834_; 
lean_dec(v___y_807_);
v___x_834_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__29));
v___y_766_ = v___y_801_;
v___y_767_ = v___x_829_;
v___y_768_ = v___x_824_;
v___y_769_ = v___y_805_;
v___y_770_ = v___x_826_;
v___y_771_ = v___y_799_;
v___y_772_ = v___x_823_;
v___y_773_ = v___x_821_;
v___y_774_ = v___x_831_;
v___y_775_ = v___x_828_;
v___y_776_ = v___y_804_;
v___y_777_ = v___y_808_;
v___y_778_ = v___y_809_;
v___y_779_ = v___x_834_;
goto v___jp_765_;
}
}
v___jp_835_:
{
lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; uint8_t v___x_844_; 
v___x_841_ = lean_unsigned_to_nat(4u);
v___x_842_ = l_Lean_Syntax_getArg(v_x_762_, v___x_841_);
v___x_843_ = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__24));
lean_inc(v___x_842_);
v___x_844_ = l_Lean_Syntax_isOfKind(v___x_842_, v___x_843_);
if (v___x_844_ == 0)
{
lean_object* v___x_845_; lean_object* v___x_846_; 
lean_dec(v___x_842_);
lean_dec(v_phase_x3f_838_);
lean_dec(v___y_837_);
lean_dec(v___y_836_);
lean_dec(v_x_762_);
v___x_845_ = lean_box(1);
v___x_846_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_846_, 0, v___x_845_);
lean_ctor_set(v___x_846_, 1, v___y_840_);
return v___x_846_;
}
else
{
lean_object* v_ref_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; uint8_t v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; 
v_ref_847_ = lean_ctor_get(v___y_839_, 5);
v___x_848_ = lean_unsigned_to_nat(6u);
v___x_849_ = l_Lean_Syntax_getArg(v_x_762_, v___x_848_);
v___x_850_ = lean_unsigned_to_nat(9u);
v___x_851_ = l_Lean_Syntax_getArg(v_x_762_, v___x_850_);
lean_dec(v_x_762_);
v___x_852_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__5));
v___x_853_ = 0;
v___x_854_ = l_Lean_SourceInfo_fromRef(v_ref_847_, v___x_853_);
v___x_855_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__22));
v___x_856_ = ((lean_object*)(l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__1));
v___x_857_ = lean_obj_once(&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__28, &l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__28_once, _init_l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__28);
if (lean_obj_tag(v___y_836_) == 1)
{
lean_object* v_val_858_; lean_object* v___x_859_; 
v_val_858_ = lean_ctor_get(v___y_836_, 0);
lean_inc(v_val_858_);
lean_dec_ref_known(v___y_836_, 1);
v___x_859_ = l_Array_mkArray1___redArg(v_val_858_);
v___y_799_ = v___x_857_;
v___y_800_ = v___x_851_;
v___y_801_ = v___x_842_;
v___y_802_ = v___x_849_;
v___y_803_ = v___x_856_;
v___y_804_ = v___y_837_;
v___y_805_ = v___y_840_;
v___y_806_ = v___x_852_;
v___y_807_ = v_phase_x3f_838_;
v___y_808_ = v___x_854_;
v___y_809_ = v___x_855_;
v___y_810_ = v___x_859_;
goto v___jp_798_;
}
else
{
lean_object* v___x_860_; 
lean_dec(v___y_836_);
v___x_860_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__29));
v___y_799_ = v___x_857_;
v___y_800_ = v___x_851_;
v___y_801_ = v___x_842_;
v___y_802_ = v___x_849_;
v___y_803_ = v___x_856_;
v___y_804_ = v___y_837_;
v___y_805_ = v___y_840_;
v___y_806_ = v___x_852_;
v___y_807_ = v_phase_x3f_838_;
v___y_808_ = v___x_854_;
v___y_809_ = v___x_855_;
v___y_810_ = v___x_860_;
goto v___jp_798_;
}
}
}
v___jp_861_:
{
lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; uint8_t v___x_868_; 
v___x_865_ = lean_unsigned_to_nat(1u);
v___x_866_ = l_Lean_Syntax_getArg(v_x_762_, v___x_865_);
v___x_867_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__7));
lean_inc(v___x_866_);
v___x_868_ = l_Lean_Syntax_isOfKind(v___x_866_, v___x_867_);
if (v___x_868_ == 0)
{
lean_object* v___x_869_; lean_object* v___x_870_; 
lean_dec(v___x_866_);
lean_dec(v_doc_x3f_862_);
lean_dec(v_x_762_);
v___x_869_ = lean_box(1);
v___x_870_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_870_, 0, v___x_869_);
lean_ctor_set(v___x_870_, 1, v___y_864_);
return v___x_870_;
}
else
{
lean_object* v___x_871_; lean_object* v___x_872_; uint8_t v___x_873_; 
v___x_871_ = lean_unsigned_to_nat(3u);
v___x_872_ = l_Lean_Syntax_getArg(v_x_762_, v___x_871_);
v___x_873_ = l_Lean_Syntax_isNone(v___x_872_);
if (v___x_873_ == 0)
{
uint8_t v___x_874_; 
lean_inc(v___x_872_);
v___x_874_ = l_Lean_Syntax_matchesNull(v___x_872_, v___x_865_);
if (v___x_874_ == 0)
{
lean_object* v___x_875_; lean_object* v___x_876_; 
lean_dec(v___x_872_);
lean_dec(v___x_866_);
lean_dec(v_doc_x3f_862_);
lean_dec(v_x_762_);
v___x_875_ = lean_box(1);
v___x_876_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_876_, 0, v___x_875_);
lean_ctor_set(v___x_876_, 1, v___y_864_);
return v___x_876_;
}
else
{
lean_object* v_phase_x3f_877_; lean_object* v___x_878_; 
v_phase_x3f_877_ = l_Lean_Syntax_getArg(v___x_872_, v___x_797_);
lean_dec(v___x_872_);
v___x_878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_878_, 0, v_phase_x3f_877_);
v___y_836_ = v_doc_x3f_862_;
v___y_837_ = v___x_866_;
v_phase_x3f_838_ = v___x_878_;
v___y_839_ = v___y_863_;
v___y_840_ = v___y_864_;
goto v___jp_835_;
}
}
else
{
lean_object* v___x_879_; 
lean_dec(v___x_872_);
v___x_879_ = lean_box(0);
v___y_836_ = v_doc_x3f_862_;
v___y_837_ = v___x_866_;
v_phase_x3f_838_ = v___x_879_;
v___y_839_ = v___y_863_;
v___y_840_ = v___y_864_;
goto v___jp_835_;
}
}
}
}
v___jp_765_:
{
lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; 
lean_inc_ref(v___y_771_);
v___x_780_ = l_Array_append___redArg(v___y_771_, v___y_779_);
lean_dec_ref(v___y_779_);
lean_inc_n(v___y_778_, 4);
lean_inc_n(v___y_777_, 7);
v___x_781_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_781_, 0, v___y_777_);
lean_ctor_set(v___x_781_, 1, v___y_778_);
lean_ctor_set(v___x_781_, 2, v___x_780_);
lean_inc(v___y_767_);
v___x_782_ = l_Lean_Syntax_node2(v___y_777_, v___y_767_, v___y_774_, v___x_781_);
v___x_783_ = l_Lean_Syntax_node2(v___y_777_, v___y_775_, v___y_776_, v___x_782_);
v___x_784_ = l_Lean_Syntax_node1(v___y_777_, v___y_778_, v___x_783_);
v___x_785_ = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__0));
v___x_786_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_786_, 0, v___y_777_);
lean_ctor_set(v___x_786_, 1, v___x_785_);
v___x_787_ = l_Lean_Syntax_node1(v___y_777_, v___y_778_, v___y_766_);
lean_inc(v___y_772_);
v___x_788_ = l_Lean_Syntax_node5(v___y_777_, v___y_772_, v___y_768_, v___y_770_, v___x_784_, v___x_786_, v___x_787_);
v___x_789_ = l_Lean_Syntax_node2(v___y_777_, v___y_778_, v___y_773_, v___x_788_);
v___x_790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_790_, 0, v___x_789_);
lean_ctor_set(v___x_790_, 1, v___y_769_);
return v___x_790_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Builtin__cbv__simproc_________x28___x29_x3a_x3d____1___boxed(lean_object* v_x_894_, lean_object* v_a_895_, lean_object* v_a_896_){
_start:
{
lean_object* v_res_897_; 
v_res_897_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Builtin__cbv__simproc_________x28___x29_x3a_x3d____1(v_x_894_, v_a_895_, v_a_896_);
lean_dec_ref(v_a_895_);
return v_res_897_;
}
}
lean_object* runtime_initialize_Init_Tactics(uint8_t builtin);
lean_object* runtime_initialize_Init_Meta_Defs(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_CbvSimproc(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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

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
static const lean_string_object l_Lean_Parser_cbvSimprocEval___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "cbvSimprocEval"};
static const lean_object* l_Lean_Parser_cbvSimprocEval___closed__0 = (const lean_object*)&l_Lean_Parser_cbvSimprocEval___closed__0_value;
static const lean_string_object l_Lean_Parser_cbvSimprocEval___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Parser_cbvSimprocEval___closed__1 = (const lean_object*)&l_Lean_Parser_cbvSimprocEval___closed__1_value;
static const lean_string_object l_Lean_Parser_cbvSimprocEval___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Parser_cbvSimprocEval___closed__2 = (const lean_object*)&l_Lean_Parser_cbvSimprocEval___closed__2_value;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
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
extern lean_object* l_Lean_Parser_Tactic_simpPost;
static lean_once_cell_t l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__19;
extern lean_object* l_Lean_Parser_Tactic_simpPre;
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Array_mkArray0(lean_object*);
static lean_once_cell_t l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__28;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static const lean_array_object l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__29 = (const lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__29_value;
static const lean_ctor_object l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_cbvSimprocEval___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__30_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__30_value_aux_0),((lean_object*)&l_Lean_Parser_cbvSimprocEval___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__30_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__30_value_aux_1),((lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__23_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__30_value_aux_2),((lean_object*)&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__6_value),LEAN_SCALAR_PTR_LITERAL(44, 76, 179, 33, 27, 4, 201, 125)}};
static const lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__30 = (const lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__30_value;
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_syntax_ident(lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Array_mkArray1___redArg(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
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
lean_object* l_Lean_Syntax_node8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Builtin__cbv__simproc_________x28___x29_x3a_x3d____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "builtin_cbv_simproc_decl"};
static const lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Builtin__cbv__simproc_________x28___x29_x3a_x3d____1___closed__0 = (const lean_object*)&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Builtin__cbv__simproc_________x28___x29_x3a_x3d____1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Builtin__cbv__simproc_________x28___x29_x3a_x3d____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Builtin__cbv__simproc_________x28___x29_x3a_x3d____1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__19(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = ((lean_object*)(l_Lean_Parser_cbvSimprocEval));
x_2 = l_Lean_Parser_Tactic_simpPost;
x_3 = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__18));
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__20(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__19, &l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__19_once, _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__19);
x_2 = l_Lean_Parser_Tactic_simpPre;
x_3 = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__18));
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__21(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__20, &l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__20_once, _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__20);
x_2 = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__5));
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__22(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__21, &l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__21_once, _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__21);
x_2 = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__16));
x_3 = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3));
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__26(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__25));
x_2 = lean_obj_once(&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__22, &l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__22_once, _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__22);
x_3 = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3));
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__29(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__28));
x_2 = lean_obj_once(&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__26, &l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__26_once, _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__26);
x_3 = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3));
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__33(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__32));
x_2 = lean_obj_once(&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__29, &l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__29_once, _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__29);
x_3 = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3));
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__36(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__35));
x_2 = lean_obj_once(&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__33, &l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__33_once, _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__33);
x_3 = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3));
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__39(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__38));
x_2 = lean_obj_once(&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__36, &l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__36_once, _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__36);
x_3 = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3));
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__40(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__32));
x_2 = lean_obj_once(&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__39, &l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__39_once, _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__39);
x_3 = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3));
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__41(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__40, &l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__40_once, _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__40);
x_2 = lean_unsigned_to_nat(1022u);
x_3 = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__1));
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d__(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__41, &l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__41_once, _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__41);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__21, &l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__21_once, _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__21);
x_2 = ((lean_object*)(l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__4));
x_3 = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3));
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__25));
x_2 = lean_obj_once(&l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__5, &l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__5_once, _init_l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__5);
x_3 = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3));
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__28));
x_2 = lean_obj_once(&l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__6, &l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__6_once, _init_l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__6);
x_3 = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3));
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__32));
x_2 = lean_obj_once(&l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__7, &l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__7_once, _init_l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__7);
x_3 = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3));
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__9(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__35));
x_2 = lean_obj_once(&l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__8, &l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__8_once, _init_l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__8);
x_3 = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3));
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__10(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__38));
x_2 = lean_obj_once(&l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__9, &l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__9_once, _init_l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__9);
x_3 = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3));
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__11(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__32));
x_2 = lean_obj_once(&l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__10, &l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__10_once, _init_l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__10);
x_3 = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3));
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__12(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__11, &l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__11_once, _init_l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__11);
x_2 = lean_unsigned_to_nat(1022u);
x_3 = ((lean_object*)(l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__1));
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d__(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__12, &l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__12_once, _init_l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__12);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Attr_cbvSimprocAttr___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__21, &l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__21_once, _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__21);
x_2 = ((lean_object*)(l_Lean_Parser_Attr_cbvSimprocAttr___closed__4));
x_3 = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3));
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Attr_cbvSimprocAttr___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_Lean_Parser_Attr_cbvSimprocAttr___closed__5, &l_Lean_Parser_Attr_cbvSimprocAttr___closed__5_once, _init_l_Lean_Parser_Attr_cbvSimprocAttr___closed__5);
x_2 = lean_unsigned_to_nat(1022u);
x_3 = ((lean_object*)(l_Lean_Parser_Attr_cbvSimprocAttr___closed__2));
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Attr_cbvSimprocAttr(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_Parser_Attr_cbvSimprocAttr___closed__6, &l_Lean_Parser_Attr_cbvSimprocAttr___closed__6_once, _init_l_Lean_Parser_Attr_cbvSimprocAttr___closed__6);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__21, &l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__21_once, _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__21);
x_2 = ((lean_object*)(l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__3));
x_3 = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3));
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__4, &l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__4_once, _init_l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__4);
x_2 = lean_unsigned_to_nat(1022u);
x_3 = ((lean_object*)(l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__1));
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Attr_cbvSimprocBuiltinAttr(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__5, &l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__5_once, _init_l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__5);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__28(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Array_mkArray0(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_87; uint8_t x_88; 
x_4 = ((lean_object*)(l_Lean_Parser_cbvSimprocEval___closed__1));
x_5 = ((lean_object*)(l_Lean_Parser_cbvSimprocEval___closed__2));
x_87 = ((lean_object*)(l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__1));
lean_inc(x_1);
x_88 = l_Lean_Syntax_isOfKind(x_1, x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; 
lean_dec(x_1);
x_89 = lean_box(1);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_3);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_91 = lean_unsigned_to_nat(0u);
x_92 = l_Lean_Syntax_getArg(x_1, x_91);
x_93 = l_Lean_Syntax_isNone(x_92);
if (x_93 == 0)
{
lean_object* x_94; uint8_t x_95; 
x_94 = lean_unsigned_to_nat(1u);
lean_inc(x_92);
x_95 = l_Lean_Syntax_matchesNull(x_92, x_94);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_92);
lean_dec(x_1);
x_96 = lean_box(1);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_3);
return x_97;
}
else
{
lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_98 = l_Lean_Syntax_getArg(x_92, x_91);
lean_dec(x_92);
x_99 = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__30));
lean_inc(x_98);
x_100 = l_Lean_Syntax_isOfKind(x_98, x_99);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; 
lean_dec(x_98);
lean_dec(x_1);
x_101 = lean_box(1);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_3);
return x_102;
}
else
{
lean_object* x_103; 
x_103 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_103, 0, x_98);
x_61 = x_103;
x_62 = x_2;
x_63 = x_3;
goto block_86;
}
}
}
else
{
lean_object* x_104; 
lean_dec(x_92);
x_104 = lean_box(0);
x_61 = x_104;
x_62 = x_2;
x_63 = x_3;
goto block_86;
}
}
block_60:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_inc_ref(x_6);
x_18 = l_Array_append___redArg(x_6, x_17);
lean_dec_ref(x_17);
lean_inc(x_12);
lean_inc(x_8);
x_19 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_12);
lean_ctor_set(x_19, 2, x_18);
lean_inc(x_12);
lean_inc(x_8);
x_20 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_20, 0, x_8);
lean_ctor_set(x_20, 1, x_12);
lean_ctor_set(x_20, 2, x_6);
x_21 = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__0));
lean_inc_ref(x_11);
x_22 = l_Lean_Name_mkStr4(x_4, x_5, x_11, x_21);
lean_inc(x_8);
x_23 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_23, 0, x_8);
lean_ctor_set(x_23, 1, x_21);
lean_inc(x_8);
x_24 = l_Lean_Syntax_node1(x_8, x_22, x_23);
lean_inc(x_12);
lean_inc(x_8);
x_25 = l_Lean_Syntax_node1(x_8, x_12, x_24);
lean_inc_ref_n(x_20, 5);
lean_inc(x_8);
x_26 = l_Lean_Syntax_node7(x_8, x_15, x_19, x_20, x_20, x_20, x_25, x_20, x_20);
x_27 = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__1));
lean_inc_ref(x_11);
x_28 = l_Lean_Name_mkStr4(x_4, x_5, x_11, x_27);
x_29 = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__2));
lean_inc(x_8);
x_30 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_30, 0, x_8);
lean_ctor_set(x_30, 1, x_29);
x_31 = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__3));
lean_inc_ref(x_11);
x_32 = l_Lean_Name_mkStr4(x_4, x_5, x_11, x_31);
lean_inc_ref(x_20);
lean_inc(x_10);
lean_inc(x_8);
x_33 = l_Lean_Syntax_node2(x_8, x_32, x_10, x_20);
x_34 = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__4));
lean_inc_ref(x_11);
x_35 = l_Lean_Name_mkStr4(x_4, x_5, x_11, x_34);
x_36 = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__7));
x_37 = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__8));
lean_inc(x_8);
x_38 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_38, 0, x_8);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_mk_syntax_ident(x_9);
lean_inc(x_8);
x_40 = l_Lean_Syntax_node2(x_8, x_36, x_38, x_39);
lean_inc(x_12);
lean_inc(x_8);
x_41 = l_Lean_Syntax_node1(x_8, x_12, x_40);
lean_inc_ref(x_20);
lean_inc(x_8);
x_42 = l_Lean_Syntax_node2(x_8, x_35, x_20, x_41);
x_43 = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__9));
x_44 = l_Lean_Name_mkStr4(x_4, x_5, x_11, x_43);
x_45 = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__10));
lean_inc(x_8);
x_46 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_46, 0, x_8);
lean_ctor_set(x_46, 1, x_45);
x_47 = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__13));
lean_inc_ref_n(x_20, 2);
lean_inc(x_8);
x_48 = l_Lean_Syntax_node2(x_8, x_47, x_20, x_20);
lean_inc_ref(x_20);
lean_inc(x_8);
x_49 = l_Lean_Syntax_node4(x_8, x_44, x_46, x_13, x_48, x_20);
lean_inc(x_8);
x_50 = l_Lean_Syntax_node5(x_8, x_28, x_30, x_33, x_42, x_49, x_20);
lean_inc(x_8);
x_51 = l_Lean_Syntax_node2(x_8, x_7, x_26, x_50);
x_52 = ((lean_object*)(l_Lean_Parser_cbvSimprocPattern___closed__1));
x_53 = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__14));
lean_inc(x_8);
x_54 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_54, 0, x_8);
lean_ctor_set(x_54, 1, x_53);
x_55 = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__15));
lean_inc(x_8);
x_56 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_56, 0, x_8);
lean_ctor_set(x_56, 1, x_55);
lean_inc(x_8);
x_57 = l_Lean_Syntax_node4(x_8, x_52, x_54, x_14, x_56, x_10);
x_58 = l_Lean_Syntax_node2(x_8, x_12, x_51, x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_16);
return x_59;
}
block_86:
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_64 = lean_unsigned_to_nat(2u);
x_65 = l_Lean_Syntax_getArg(x_1, x_64);
x_66 = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__24));
lean_inc(x_65);
x_67 = l_Lean_Syntax_isOfKind(x_65, x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
lean_dec(x_65);
lean_dec(x_61);
lean_dec(x_1);
x_68 = lean_box(1);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_63);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_70 = lean_ctor_get(x_62, 5);
x_71 = lean_unsigned_to_nat(4u);
x_72 = l_Lean_Syntax_getArg(x_1, x_71);
x_73 = lean_unsigned_to_nat(7u);
x_74 = l_Lean_Syntax_getArg(x_1, x_73);
lean_dec(x_1);
x_75 = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__20));
x_76 = 0;
x_77 = l_Lean_SourceInfo_fromRef(x_70, x_76);
x_78 = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__22));
x_79 = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__23));
x_80 = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__25));
x_81 = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__27));
x_82 = lean_obj_once(&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__28, &l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__28_once, _init_l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__28);
if (lean_obj_tag(x_61) == 1)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_61, 0);
lean_inc(x_83);
lean_dec_ref(x_61);
x_84 = l_Array_mkArray1___redArg(x_83);
x_6 = x_82;
x_7 = x_80;
x_8 = x_77;
x_9 = x_75;
x_10 = x_65;
x_11 = x_79;
x_12 = x_78;
x_13 = x_74;
x_14 = x_72;
x_15 = x_81;
x_16 = x_63;
x_17 = x_84;
goto block_60;
}
else
{
lean_object* x_85; 
lean_dec(x_61);
x_85 = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__29));
x_6 = x_82;
x_7 = x_80;
x_8 = x_77;
x_9 = x_75;
x_10 = x_65;
x_11 = x_79;
x_12 = x_78;
x_13 = x_74;
x_14 = x_72;
x_15 = x_81;
x_16 = x_63;
x_17 = x_85;
goto block_60;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d____1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_82; uint8_t x_83; 
x_4 = ((lean_object*)(l_Lean_Parser_cbvSimprocEval___closed__1));
x_5 = ((lean_object*)(l_Lean_Parser_cbvSimprocEval___closed__2));
x_82 = ((lean_object*)(l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__1));
lean_inc(x_1);
x_83 = l_Lean_Syntax_isOfKind(x_1, x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; 
lean_dec(x_1);
x_84 = lean_box(1);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_3);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_86 = lean_unsigned_to_nat(0u);
x_87 = l_Lean_Syntax_getArg(x_1, x_86);
x_88 = l_Lean_Syntax_isNone(x_87);
if (x_88 == 0)
{
lean_object* x_89; uint8_t x_90; 
x_89 = lean_unsigned_to_nat(1u);
lean_inc(x_87);
x_90 = l_Lean_Syntax_matchesNull(x_87, x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; 
lean_dec(x_87);
lean_dec(x_1);
x_91 = lean_box(1);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_3);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_93 = l_Lean_Syntax_getArg(x_87, x_86);
lean_dec(x_87);
x_94 = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__30));
lean_inc(x_93);
x_95 = l_Lean_Syntax_isOfKind(x_93, x_94);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_93);
lean_dec(x_1);
x_96 = lean_box(1);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_3);
return x_97;
}
else
{
lean_object* x_98; 
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_93);
x_56 = x_98;
x_57 = x_2;
x_58 = x_3;
goto block_81;
}
}
}
else
{
lean_object* x_99; 
lean_dec(x_87);
x_99 = lean_box(0);
x_56 = x_99;
x_57 = x_2;
x_58 = x_3;
goto block_81;
}
}
block_55:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_inc_ref(x_10);
x_18 = l_Array_append___redArg(x_10, x_17);
lean_dec_ref(x_17);
lean_inc(x_6);
lean_inc(x_16);
x_19 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_6);
lean_ctor_set(x_19, 2, x_18);
lean_inc(x_6);
lean_inc(x_16);
x_20 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_6);
lean_ctor_set(x_20, 2, x_10);
lean_inc_ref_n(x_20, 6);
lean_inc(x_16);
x_21 = l_Lean_Syntax_node7(x_16, x_13, x_19, x_20, x_20, x_20, x_20, x_20, x_20);
x_22 = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__1));
lean_inc_ref(x_12);
x_23 = l_Lean_Name_mkStr4(x_4, x_5, x_12, x_22);
x_24 = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__2));
lean_inc(x_16);
x_25 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_25, 0, x_16);
lean_ctor_set(x_25, 1, x_24);
x_26 = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__3));
lean_inc_ref(x_12);
x_27 = l_Lean_Name_mkStr4(x_4, x_5, x_12, x_26);
lean_inc_ref(x_20);
lean_inc(x_11);
lean_inc(x_16);
x_28 = l_Lean_Syntax_node2(x_16, x_27, x_11, x_20);
x_29 = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__4));
lean_inc_ref(x_12);
x_30 = l_Lean_Name_mkStr4(x_4, x_5, x_12, x_29);
x_31 = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__7));
x_32 = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__8));
lean_inc(x_16);
x_33 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_33, 0, x_16);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_mk_syntax_ident(x_15);
lean_inc(x_16);
x_35 = l_Lean_Syntax_node2(x_16, x_31, x_33, x_34);
lean_inc(x_6);
lean_inc(x_16);
x_36 = l_Lean_Syntax_node1(x_16, x_6, x_35);
lean_inc_ref(x_20);
lean_inc(x_16);
x_37 = l_Lean_Syntax_node2(x_16, x_30, x_20, x_36);
x_38 = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__9));
x_39 = l_Lean_Name_mkStr4(x_4, x_5, x_12, x_38);
x_40 = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__10));
lean_inc(x_16);
x_41 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_41, 0, x_16);
lean_ctor_set(x_41, 1, x_40);
x_42 = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__13));
lean_inc_ref_n(x_20, 2);
lean_inc(x_16);
x_43 = l_Lean_Syntax_node2(x_16, x_42, x_20, x_20);
lean_inc_ref(x_20);
lean_inc(x_16);
x_44 = l_Lean_Syntax_node4(x_16, x_39, x_41, x_14, x_43, x_20);
lean_inc(x_16);
x_45 = l_Lean_Syntax_node5(x_16, x_23, x_25, x_28, x_37, x_44, x_20);
lean_inc(x_16);
x_46 = l_Lean_Syntax_node2(x_16, x_9, x_21, x_45);
x_47 = ((lean_object*)(l_Lean_Parser_cbvSimprocPatternBuiltin___closed__1));
x_48 = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__0));
lean_inc(x_16);
x_49 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_49, 0, x_16);
lean_ctor_set(x_49, 1, x_48);
x_50 = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__15));
lean_inc(x_16);
x_51 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_51, 0, x_16);
lean_ctor_set(x_51, 1, x_50);
lean_inc(x_16);
x_52 = l_Lean_Syntax_node4(x_16, x_47, x_49, x_8, x_51, x_11);
x_53 = l_Lean_Syntax_node2(x_16, x_6, x_46, x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_7);
return x_54;
}
block_81:
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_59 = lean_unsigned_to_nat(2u);
x_60 = l_Lean_Syntax_getArg(x_1, x_59);
x_61 = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__24));
lean_inc(x_60);
x_62 = l_Lean_Syntax_isOfKind(x_60, x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_60);
lean_dec(x_56);
lean_dec(x_1);
x_63 = lean_box(1);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_58);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_65 = lean_ctor_get(x_57, 5);
x_66 = lean_unsigned_to_nat(4u);
x_67 = l_Lean_Syntax_getArg(x_1, x_66);
x_68 = lean_unsigned_to_nat(7u);
x_69 = l_Lean_Syntax_getArg(x_1, x_68);
lean_dec(x_1);
x_70 = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__20));
x_71 = 0;
x_72 = l_Lean_SourceInfo_fromRef(x_65, x_71);
x_73 = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__22));
x_74 = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__23));
x_75 = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__25));
x_76 = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__27));
x_77 = lean_obj_once(&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__28, &l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__28_once, _init_l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__28);
if (lean_obj_tag(x_56) == 1)
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_56, 0);
lean_inc(x_78);
lean_dec_ref(x_56);
x_79 = l_Array_mkArray1___redArg(x_78);
x_6 = x_73;
x_7 = x_58;
x_8 = x_67;
x_9 = x_75;
x_10 = x_77;
x_11 = x_60;
x_12 = x_74;
x_13 = x_76;
x_14 = x_69;
x_15 = x_70;
x_16 = x_72;
x_17 = x_79;
goto block_55;
}
else
{
lean_object* x_80; 
lean_dec(x_56);
x_80 = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__29));
x_6 = x_73;
x_7 = x_58;
x_8 = x_67;
x_9 = x_75;
x_10 = x_77;
x_11 = x_60;
x_12 = x_74;
x_13 = x_76;
x_14 = x_69;
x_15 = x_70;
x_16 = x_72;
x_17 = x_80;
goto block_55;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d____1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d____1(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = ((lean_object*)(l_Lean_Parser_cbvSimprocEval___closed__1));
x_31 = ((lean_object*)(l_Lean_Parser_cbvSimprocEval___closed__2));
x_32 = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__1));
lean_inc(x_1);
x_33 = l_Lean_Syntax_isOfKind(x_1, x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_1);
x_34 = lean_box(1);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_3);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_119; uint8_t x_120; 
x_36 = lean_unsigned_to_nat(0u);
x_119 = l_Lean_Syntax_getArg(x_1, x_36);
x_120 = l_Lean_Syntax_isNone(x_119);
if (x_120 == 0)
{
lean_object* x_121; uint8_t x_122; 
x_121 = lean_unsigned_to_nat(1u);
lean_inc(x_119);
x_122 = l_Lean_Syntax_matchesNull(x_119, x_121);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; 
lean_dec(x_119);
lean_dec(x_1);
x_123 = lean_box(1);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_3);
return x_124;
}
else
{
lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_125 = l_Lean_Syntax_getArg(x_119, x_36);
lean_dec(x_119);
x_126 = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__30));
lean_inc(x_125);
x_127 = l_Lean_Syntax_isOfKind(x_125, x_126);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; 
lean_dec(x_125);
lean_dec(x_1);
x_128 = lean_box(1);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_3);
return x_129;
}
else
{
lean_object* x_130; 
x_130 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_130, 0, x_125);
x_100 = x_130;
x_101 = x_2;
x_102 = x_3;
goto block_118;
}
}
}
else
{
lean_object* x_131; 
lean_dec(x_119);
x_131 = lean_box(0);
x_100 = x_131;
x_101 = x_2;
x_102 = x_3;
goto block_118;
}
block_73:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_inc_ref(x_46);
x_49 = l_Array_append___redArg(x_46, x_48);
lean_dec_ref(x_48);
lean_inc(x_45);
lean_inc(x_47);
x_50 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_45);
lean_ctor_set(x_50, 2, x_49);
x_51 = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__1));
lean_inc(x_47);
x_52 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_52, 0, x_47);
lean_ctor_set(x_52, 1, x_51);
x_53 = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__2));
lean_inc(x_47);
x_54 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_54, 0, x_47);
lean_ctor_set(x_54, 1, x_53);
x_55 = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__34));
lean_inc(x_47);
x_56 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_56, 0, x_47);
lean_ctor_set(x_56, 1, x_55);
x_57 = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__10));
lean_inc(x_47);
x_58 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_58, 0, x_47);
lean_ctor_set(x_58, 1, x_57);
lean_inc(x_40);
lean_inc(x_47);
x_59 = l_Lean_Syntax_node8(x_47, x_42, x_50, x_52, x_40, x_54, x_37, x_56, x_58, x_43);
x_60 = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__3));
x_61 = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__4));
lean_inc(x_47);
x_62 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_62, 0, x_47);
lean_ctor_set(x_62, 1, x_60);
x_63 = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__5));
lean_inc(x_47);
x_64 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_64, 0, x_47);
lean_ctor_set(x_64, 1, x_63);
x_65 = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__6));
x_66 = l_Lean_Name_mkStr4(x_30, x_31, x_38, x_65);
x_67 = ((lean_object*)(l_Lean_Parser_Attr_cbvSimprocAttr___closed__2));
x_68 = ((lean_object*)(l_Lean_Parser_Attr_cbvSimprocAttr___closed__3));
lean_inc(x_47);
x_69 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_69, 0, x_47);
lean_ctor_set(x_69, 1, x_68);
if (lean_obj_tag(x_44) == 1)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_44, 0);
lean_inc(x_70);
lean_dec_ref(x_44);
x_71 = l_Array_mkArray1___redArg(x_70);
x_4 = x_39;
x_5 = x_59;
x_6 = x_67;
x_7 = x_64;
x_8 = x_69;
x_9 = x_61;
x_10 = x_46;
x_11 = x_40;
x_12 = x_66;
x_13 = x_41;
x_14 = x_62;
x_15 = x_45;
x_16 = x_47;
x_17 = x_71;
goto block_29;
}
else
{
lean_object* x_72; 
lean_dec(x_44);
x_72 = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__29));
x_4 = x_39;
x_5 = x_59;
x_6 = x_67;
x_7 = x_64;
x_8 = x_69;
x_9 = x_61;
x_10 = x_46;
x_11 = x_40;
x_12 = x_66;
x_13 = x_41;
x_14 = x_62;
x_15 = x_45;
x_16 = x_47;
x_17 = x_72;
goto block_29;
}
}
block_99:
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_79 = lean_unsigned_to_nat(4u);
x_80 = l_Lean_Syntax_getArg(x_1, x_79);
x_81 = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__24));
lean_inc(x_80);
x_82 = l_Lean_Syntax_isOfKind(x_80, x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; 
lean_dec(x_80);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_1);
x_83 = lean_box(1);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_78);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_85 = lean_ctor_get(x_77, 5);
x_86 = lean_unsigned_to_nat(6u);
x_87 = l_Lean_Syntax_getArg(x_1, x_86);
x_88 = lean_unsigned_to_nat(9u);
x_89 = l_Lean_Syntax_getArg(x_1, x_88);
lean_dec(x_1);
x_90 = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__5));
x_91 = 0;
x_92 = l_Lean_SourceInfo_fromRef(x_85, x_91);
x_93 = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__22));
x_94 = ((lean_object*)(l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__1));
x_95 = lean_obj_once(&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__28, &l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__28_once, _init_l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__28);
if (lean_obj_tag(x_74) == 1)
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_74, 0);
lean_inc(x_96);
lean_dec_ref(x_74);
x_97 = l_Array_mkArray1___redArg(x_96);
x_37 = x_87;
x_38 = x_90;
x_39 = x_78;
x_40 = x_80;
x_41 = x_75;
x_42 = x_94;
x_43 = x_89;
x_44 = x_76;
x_45 = x_93;
x_46 = x_95;
x_47 = x_92;
x_48 = x_97;
goto block_73;
}
else
{
lean_object* x_98; 
lean_dec(x_74);
x_98 = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__29));
x_37 = x_87;
x_38 = x_90;
x_39 = x_78;
x_40 = x_80;
x_41 = x_75;
x_42 = x_94;
x_43 = x_89;
x_44 = x_76;
x_45 = x_93;
x_46 = x_95;
x_47 = x_92;
x_48 = x_98;
goto block_73;
}
}
}
block_118:
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_103 = lean_unsigned_to_nat(1u);
x_104 = l_Lean_Syntax_getArg(x_1, x_103);
x_105 = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__7));
lean_inc(x_104);
x_106 = l_Lean_Syntax_isOfKind(x_104, x_105);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; 
lean_dec(x_104);
lean_dec(x_100);
lean_dec(x_1);
x_107 = lean_box(1);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_102);
return x_108;
}
else
{
lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_109 = lean_unsigned_to_nat(3u);
x_110 = l_Lean_Syntax_getArg(x_1, x_109);
x_111 = l_Lean_Syntax_isNone(x_110);
if (x_111 == 0)
{
uint8_t x_112; 
lean_inc(x_110);
x_112 = l_Lean_Syntax_matchesNull(x_110, x_103);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; 
lean_dec(x_110);
lean_dec(x_104);
lean_dec(x_100);
lean_dec(x_1);
x_113 = lean_box(1);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_102);
return x_114;
}
else
{
lean_object* x_115; lean_object* x_116; 
x_115 = l_Lean_Syntax_getArg(x_110, x_36);
lean_dec(x_110);
x_116 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_116, 0, x_115);
x_74 = x_100;
x_75 = x_104;
x_76 = x_116;
x_77 = x_101;
x_78 = x_102;
goto block_99;
}
}
else
{
lean_object* x_117; 
lean_dec(x_110);
x_117 = lean_box(0);
x_74 = x_100;
x_75 = x_104;
x_76 = x_117;
x_77 = x_101;
x_78 = x_102;
goto block_99;
}
}
}
}
block_29:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_18 = l_Array_append___redArg(x_10, x_17);
lean_dec_ref(x_17);
lean_inc(x_15);
lean_inc(x_16);
x_19 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_15);
lean_ctor_set(x_19, 2, x_18);
lean_inc(x_16);
x_20 = l_Lean_Syntax_node2(x_16, x_6, x_8, x_19);
lean_inc(x_16);
x_21 = l_Lean_Syntax_node2(x_16, x_12, x_13, x_20);
lean_inc(x_15);
lean_inc(x_16);
x_22 = l_Lean_Syntax_node1(x_16, x_15, x_21);
x_23 = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__0));
lean_inc(x_16);
x_24 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_24, 0, x_16);
lean_ctor_set(x_24, 1, x_23);
lean_inc(x_15);
lean_inc(x_16);
x_25 = l_Lean_Syntax_node1(x_16, x_15, x_11);
lean_inc(x_16);
x_26 = l_Lean_Syntax_node5(x_16, x_9, x_14, x_7, x_22, x_24, x_25);
x_27 = l_Lean_Syntax_node2(x_16, x_15, x_5, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_4);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Builtin__cbv__simproc_________x28___x29_x3a_x3d____1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = ((lean_object*)(l_Lean_Parser_cbvSimprocEval___closed__1));
x_31 = ((lean_object*)(l_Lean_Parser_cbvSimprocEval___closed__2));
x_32 = ((lean_object*)(l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__1));
lean_inc(x_1);
x_33 = l_Lean_Syntax_isOfKind(x_1, x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_1);
x_34 = lean_box(1);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_3);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_119; uint8_t x_120; 
x_36 = lean_unsigned_to_nat(0u);
x_119 = l_Lean_Syntax_getArg(x_1, x_36);
x_120 = l_Lean_Syntax_isNone(x_119);
if (x_120 == 0)
{
lean_object* x_121; uint8_t x_122; 
x_121 = lean_unsigned_to_nat(1u);
lean_inc(x_119);
x_122 = l_Lean_Syntax_matchesNull(x_119, x_121);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; 
lean_dec(x_119);
lean_dec(x_1);
x_123 = lean_box(1);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_3);
return x_124;
}
else
{
lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_125 = l_Lean_Syntax_getArg(x_119, x_36);
lean_dec(x_119);
x_126 = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__30));
lean_inc(x_125);
x_127 = l_Lean_Syntax_isOfKind(x_125, x_126);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; 
lean_dec(x_125);
lean_dec(x_1);
x_128 = lean_box(1);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_3);
return x_129;
}
else
{
lean_object* x_130; 
x_130 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_130, 0, x_125);
x_100 = x_130;
x_101 = x_2;
x_102 = x_3;
goto block_118;
}
}
}
else
{
lean_object* x_131; 
lean_dec(x_119);
x_131 = lean_box(0);
x_100 = x_131;
x_101 = x_2;
x_102 = x_3;
goto block_118;
}
block_73:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_inc_ref(x_42);
x_49 = l_Array_append___redArg(x_42, x_48);
lean_dec_ref(x_48);
lean_inc(x_44);
lean_inc(x_38);
x_50 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_50, 0, x_38);
lean_ctor_set(x_50, 1, x_44);
lean_ctor_set(x_50, 2, x_49);
x_51 = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Builtin__cbv__simproc_________x28___x29_x3a_x3d____1___closed__0));
lean_inc(x_38);
x_52 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_52, 0, x_38);
lean_ctor_set(x_52, 1, x_51);
x_53 = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__2));
lean_inc(x_38);
x_54 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_54, 0, x_38);
lean_ctor_set(x_54, 1, x_53);
x_55 = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__34));
lean_inc(x_38);
x_56 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_56, 0, x_38);
lean_ctor_set(x_56, 1, x_55);
x_57 = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__10));
lean_inc(x_38);
x_58 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_58, 0, x_38);
lean_ctor_set(x_58, 1, x_57);
lean_inc(x_46);
lean_inc(x_38);
x_59 = l_Lean_Syntax_node8(x_38, x_41, x_50, x_52, x_46, x_54, x_47, x_56, x_58, x_40);
x_60 = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__3));
x_61 = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__4));
lean_inc(x_38);
x_62 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_62, 0, x_38);
lean_ctor_set(x_62, 1, x_60);
x_63 = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__5));
lean_inc(x_38);
x_64 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_64, 0, x_38);
lean_ctor_set(x_64, 1, x_63);
x_65 = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__6));
x_66 = l_Lean_Name_mkStr4(x_30, x_31, x_37, x_65);
x_67 = ((lean_object*)(l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__1));
x_68 = ((lean_object*)(l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__2));
lean_inc(x_38);
x_69 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_69, 0, x_38);
lean_ctor_set(x_69, 1, x_68);
if (lean_obj_tag(x_45) == 1)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_45, 0);
lean_inc(x_70);
lean_dec_ref(x_45);
x_71 = l_Array_mkArray1___redArg(x_70);
x_4 = x_38;
x_5 = x_39;
x_6 = x_64;
x_7 = x_42;
x_8 = x_66;
x_9 = x_69;
x_10 = x_46;
x_11 = x_61;
x_12 = x_59;
x_13 = x_43;
x_14 = x_44;
x_15 = x_62;
x_16 = x_67;
x_17 = x_71;
goto block_29;
}
else
{
lean_object* x_72; 
lean_dec(x_45);
x_72 = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__29));
x_4 = x_38;
x_5 = x_39;
x_6 = x_64;
x_7 = x_42;
x_8 = x_66;
x_9 = x_69;
x_10 = x_46;
x_11 = x_61;
x_12 = x_59;
x_13 = x_43;
x_14 = x_44;
x_15 = x_62;
x_16 = x_67;
x_17 = x_72;
goto block_29;
}
}
block_99:
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_79 = lean_unsigned_to_nat(4u);
x_80 = l_Lean_Syntax_getArg(x_1, x_79);
x_81 = ((lean_object*)(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__24));
lean_inc(x_80);
x_82 = l_Lean_Syntax_isOfKind(x_80, x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; 
lean_dec(x_80);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_1);
x_83 = lean_box(1);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_78);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_85 = lean_ctor_get(x_77, 5);
x_86 = lean_unsigned_to_nat(6u);
x_87 = l_Lean_Syntax_getArg(x_1, x_86);
x_88 = lean_unsigned_to_nat(9u);
x_89 = l_Lean_Syntax_getArg(x_1, x_88);
lean_dec(x_1);
x_90 = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__5));
x_91 = 0;
x_92 = l_Lean_SourceInfo_fromRef(x_85, x_91);
x_93 = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__22));
x_94 = ((lean_object*)(l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__1));
x_95 = lean_obj_once(&l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__28, &l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__28_once, _init_l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__28);
if (lean_obj_tag(x_74) == 1)
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_74, 0);
lean_inc(x_96);
lean_dec_ref(x_74);
x_97 = l_Array_mkArray1___redArg(x_96);
x_37 = x_90;
x_38 = x_92;
x_39 = x_75;
x_40 = x_89;
x_41 = x_94;
x_42 = x_95;
x_43 = x_78;
x_44 = x_93;
x_45 = x_76;
x_46 = x_80;
x_47 = x_87;
x_48 = x_97;
goto block_73;
}
else
{
lean_object* x_98; 
lean_dec(x_74);
x_98 = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__29));
x_37 = x_90;
x_38 = x_92;
x_39 = x_75;
x_40 = x_89;
x_41 = x_94;
x_42 = x_95;
x_43 = x_78;
x_44 = x_93;
x_45 = x_76;
x_46 = x_80;
x_47 = x_87;
x_48 = x_98;
goto block_73;
}
}
}
block_118:
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_103 = lean_unsigned_to_nat(1u);
x_104 = l_Lean_Syntax_getArg(x_1, x_103);
x_105 = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__7));
lean_inc(x_104);
x_106 = l_Lean_Syntax_isOfKind(x_104, x_105);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; 
lean_dec(x_104);
lean_dec(x_100);
lean_dec(x_1);
x_107 = lean_box(1);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_102);
return x_108;
}
else
{
lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_109 = lean_unsigned_to_nat(3u);
x_110 = l_Lean_Syntax_getArg(x_1, x_109);
x_111 = l_Lean_Syntax_isNone(x_110);
if (x_111 == 0)
{
uint8_t x_112; 
lean_inc(x_110);
x_112 = l_Lean_Syntax_matchesNull(x_110, x_103);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; 
lean_dec(x_110);
lean_dec(x_104);
lean_dec(x_100);
lean_dec(x_1);
x_113 = lean_box(1);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_102);
return x_114;
}
else
{
lean_object* x_115; lean_object* x_116; 
x_115 = l_Lean_Syntax_getArg(x_110, x_36);
lean_dec(x_110);
x_116 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_116, 0, x_115);
x_74 = x_100;
x_75 = x_104;
x_76 = x_116;
x_77 = x_101;
x_78 = x_102;
goto block_99;
}
}
else
{
lean_object* x_117; 
lean_dec(x_110);
x_117 = lean_box(0);
x_74 = x_100;
x_75 = x_104;
x_76 = x_117;
x_77 = x_101;
x_78 = x_102;
goto block_99;
}
}
}
}
block_29:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_18 = l_Array_append___redArg(x_7, x_17);
lean_dec_ref(x_17);
lean_inc(x_14);
lean_inc(x_4);
x_19 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_19, 0, x_4);
lean_ctor_set(x_19, 1, x_14);
lean_ctor_set(x_19, 2, x_18);
lean_inc(x_4);
x_20 = l_Lean_Syntax_node2(x_4, x_16, x_9, x_19);
lean_inc(x_4);
x_21 = l_Lean_Syntax_node2(x_4, x_8, x_5, x_20);
lean_inc(x_14);
lean_inc(x_4);
x_22 = l_Lean_Syntax_node1(x_4, x_14, x_21);
x_23 = ((lean_object*)(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__0));
lean_inc(x_4);
x_24 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_24, 0, x_4);
lean_ctor_set(x_24, 1, x_23);
lean_inc(x_14);
lean_inc(x_4);
x_25 = l_Lean_Syntax_node1(x_4, x_14, x_10);
lean_inc(x_4);
x_26 = l_Lean_Syntax_node5(x_4, x_11, x_15, x_6, x_22, x_24, x_25);
x_27 = l_Lean_Syntax_node2(x_4, x_14, x_12, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_13);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Builtin__cbv__simproc_________x28___x29_x3a_x3d____1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Builtin__cbv__simproc_________x28___x29_x3a_x3d____1(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
lean_object* runtime_initialize_Init_Tactics(uint8_t builtin);
lean_object* runtime_initialize_Init_Meta_Defs(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_CbvSimproc(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Tactics(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Meta_Defs(builtin)
;
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
res = runtime_initialize_Init_Data_ToString_Name(builtin)
;
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
res = initialize_Init_Data_ToString_Name(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Tactics(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Meta_Defs(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_CbvSimproc(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_CbvSimproc(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_CbvSimproc(builtin);
}
#ifdef __cplusplus
}
#endif

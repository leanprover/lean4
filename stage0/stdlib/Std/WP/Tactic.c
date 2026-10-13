// Lean compiler output
// Module: Std.WP.Tactic
// Imports: public import Init.Grind.Interactive public import Init.NotationExtra
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_caseArg;
extern lean_object* l_Lean_cdotTk;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_simpLemma;
extern lean_object* l_Lean_Parser_Tactic_simpErase;
extern lean_object* l_Lean_Parser_Tactic_simpStar;
extern lean_object* l_Lean_Parser_Tactic_optConfig;
extern lean_object* l_Lean_binderIdent;
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Attr_spec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Parser_Attr_spec___closed__0 = (const lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value;
static const lean_string_object l_Lean_Parser_Attr_spec___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Parser_Attr_spec___closed__1 = (const lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value;
static const lean_string_object l_Lean_Parser_Attr_spec___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l_Lean_Parser_Attr_spec___closed__2 = (const lean_object*)&l_Lean_Parser_Attr_spec___closed__2_value;
static const lean_string_object l_Lean_Parser_Attr_spec___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "spec"};
static const lean_object* l_Lean_Parser_Attr_spec___closed__3 = (const lean_object*)&l_Lean_Parser_Attr_spec___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Attr_spec___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Attr_spec___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__4_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Attr_spec___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__4_value_aux_1),((lean_object*)&l_Lean_Parser_Attr_spec___closed__2_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Parser_Attr_spec___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__4_value_aux_2),((lean_object*)&l_Lean_Parser_Attr_spec___closed__3_value),LEAN_SCALAR_PTR_LITERAL(108, 37, 203, 230, 106, 254, 64, 102)}};
static const lean_object* l_Lean_Parser_Attr_spec___closed__4 = (const lean_object*)&l_Lean_Parser_Attr_spec___closed__4_value;
static const lean_string_object l_Lean_Parser_Attr_spec___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Lean_Parser_Attr_spec___closed__5 = (const lean_object*)&l_Lean_Parser_Attr_spec___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Attr_spec___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__5_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Lean_Parser_Attr_spec___closed__6 = (const lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Attr_spec___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Attr_spec___closed__7 = (const lean_object*)&l_Lean_Parser_Attr_spec___closed__7_value;
static const lean_string_object l_Lean_Parser_Attr_spec___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "optional"};
static const lean_object* l_Lean_Parser_Attr_spec___closed__8 = (const lean_object*)&l_Lean_Parser_Attr_spec___closed__8_value;
static const lean_ctor_object l_Lean_Parser_Attr_spec___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__8_value),LEAN_SCALAR_PTR_LITERAL(233, 141, 154, 50, 143, 135, 42, 252)}};
static const lean_object* l_Lean_Parser_Attr_spec___closed__9 = (const lean_object*)&l_Lean_Parser_Attr_spec___closed__9_value;
static const lean_string_object l_Lean_Parser_Attr_spec___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "ppSpace"};
static const lean_object* l_Lean_Parser_Attr_spec___closed__10 = (const lean_object*)&l_Lean_Parser_Attr_spec___closed__10_value;
static const lean_ctor_object l_Lean_Parser_Attr_spec___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__10_value),LEAN_SCALAR_PTR_LITERAL(207, 47, 58, 43, 30, 240, 125, 246)}};
static const lean_object* l_Lean_Parser_Attr_spec___closed__11 = (const lean_object*)&l_Lean_Parser_Attr_spec___closed__11_value;
static const lean_ctor_object l_Lean_Parser_Attr_spec___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__11_value)}};
static const lean_object* l_Lean_Parser_Attr_spec___closed__12 = (const lean_object*)&l_Lean_Parser_Attr_spec___closed__12_value;
static const lean_string_object l_Lean_Parser_Attr_spec___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "prio"};
static const lean_object* l_Lean_Parser_Attr_spec___closed__13 = (const lean_object*)&l_Lean_Parser_Attr_spec___closed__13_value;
static const lean_ctor_object l_Lean_Parser_Attr_spec___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__13_value),LEAN_SCALAR_PTR_LITERAL(122, 247, 65, 238, 243, 154, 137, 247)}};
static const lean_object* l_Lean_Parser_Attr_spec___closed__14 = (const lean_object*)&l_Lean_Parser_Attr_spec___closed__14_value;
static const lean_ctor_object l_Lean_Parser_Attr_spec___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__14_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Attr_spec___closed__15 = (const lean_object*)&l_Lean_Parser_Attr_spec___closed__15_value;
static const lean_ctor_object l_Lean_Parser_Attr_spec___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Attr_spec___closed__12_value),((lean_object*)&l_Lean_Parser_Attr_spec___closed__15_value)}};
static const lean_object* l_Lean_Parser_Attr_spec___closed__16 = (const lean_object*)&l_Lean_Parser_Attr_spec___closed__16_value;
static const lean_ctor_object l_Lean_Parser_Attr_spec___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__9_value),((lean_object*)&l_Lean_Parser_Attr_spec___closed__16_value)}};
static const lean_object* l_Lean_Parser_Attr_spec___closed__17 = (const lean_object*)&l_Lean_Parser_Attr_spec___closed__17_value;
static const lean_ctor_object l_Lean_Parser_Attr_spec___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Attr_spec___closed__7_value),((lean_object*)&l_Lean_Parser_Attr_spec___closed__17_value)}};
static const lean_object* l_Lean_Parser_Attr_spec___closed__18 = (const lean_object*)&l_Lean_Parser_Attr_spec___closed__18_value;
static const lean_ctor_object l_Lean_Parser_Attr_spec___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__4_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__18_value)}};
static const lean_object* l_Lean_Parser_Attr_spec___closed__19 = (const lean_object*)&l_Lean_Parser_Attr_spec___closed__19_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Attr_spec = (const lean_object*)&l_Lean_Parser_Attr_spec___closed__19_value;
static const lean_string_object l_Lean_Parser_Tactic_invariantDotAlt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "invariantDotAlt"};
static const lean_object* l_Lean_Parser_Tactic_invariantDotAlt___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_invariantDotAlt___closed__0_value;
static const lean_string_object l_Lean_Parser_Tactic_invariantDotAlt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Parser_Tactic_invariantDotAlt___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_invariantDotAlt___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_invariantDotAlt___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_invariantDotAlt___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_invariantDotAlt___closed__2_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_invariantDotAlt___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_invariantDotAlt___closed__2_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_invariantDotAlt___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_invariantDotAlt___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_invariantDotAlt___closed__2_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_invariantDotAlt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(174, 218, 225, 197, 89, 244, 133, 64)}};
static const lean_object* l_Lean_Parser_Tactic_invariantDotAlt___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_invariantDotAlt___closed__2_value;
static const lean_string_object l_Lean_Parser_Tactic_invariantDotAlt___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ppDedent"};
static const lean_object* l_Lean_Parser_Tactic_invariantDotAlt___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_invariantDotAlt___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_invariantDotAlt___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_invariantDotAlt___closed__3_value),LEAN_SCALAR_PTR_LITERAL(242, 37, 230, 124, 106, 100, 159, 37)}};
static const lean_object* l_Lean_Parser_Tactic_invariantDotAlt___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_invariantDotAlt___closed__4_value;
static const lean_string_object l_Lean_Parser_Tactic_invariantDotAlt___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ppLine"};
static const lean_object* l_Lean_Parser_Tactic_invariantDotAlt___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_invariantDotAlt___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_invariantDotAlt___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_invariantDotAlt___closed__5_value),LEAN_SCALAR_PTR_LITERAL(117, 61, 38, 245, 158, 59, 171, 58)}};
static const lean_object* l_Lean_Parser_Tactic_invariantDotAlt___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_invariantDotAlt___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_invariantDotAlt___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_invariantDotAlt___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_invariantDotAlt___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_invariantDotAlt___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_invariantDotAlt___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_invariantDotAlt___closed__4_value),((lean_object*)&l_Lean_Parser_Tactic_invariantDotAlt___closed__7_value)}};
static const lean_object* l_Lean_Parser_Tactic_invariantDotAlt___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_invariantDotAlt___closed__8_value;
static lean_once_cell_t l_Lean_Parser_Tactic_invariantDotAlt___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_invariantDotAlt___closed__9;
static const lean_string_object l_Lean_Parser_Tactic_invariantDotAlt___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "colGe"};
static const lean_object* l_Lean_Parser_Tactic_invariantDotAlt___closed__10 = (const lean_object*)&l_Lean_Parser_Tactic_invariantDotAlt___closed__10_value;
static const lean_ctor_object l_Lean_Parser_Tactic_invariantDotAlt___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_invariantDotAlt___closed__10_value),LEAN_SCALAR_PTR_LITERAL(119, 36, 80, 74, 173, 106, 150, 68)}};
static const lean_object* l_Lean_Parser_Tactic_invariantDotAlt___closed__11 = (const lean_object*)&l_Lean_Parser_Tactic_invariantDotAlt___closed__11_value;
static const lean_ctor_object l_Lean_Parser_Tactic_invariantDotAlt___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_invariantDotAlt___closed__11_value)}};
static const lean_object* l_Lean_Parser_Tactic_invariantDotAlt___closed__12 = (const lean_object*)&l_Lean_Parser_Tactic_invariantDotAlt___closed__12_value;
static const lean_string_object l_Lean_Parser_Tactic_invariantDotAlt___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Lean_Parser_Tactic_invariantDotAlt___closed__13 = (const lean_object*)&l_Lean_Parser_Tactic_invariantDotAlt___closed__13_value;
static const lean_ctor_object l_Lean_Parser_Tactic_invariantDotAlt___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_invariantDotAlt___closed__13_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Lean_Parser_Tactic_invariantDotAlt___closed__14 = (const lean_object*)&l_Lean_Parser_Tactic_invariantDotAlt___closed__14_value;
static const lean_ctor_object l_Lean_Parser_Tactic_invariantDotAlt___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_invariantDotAlt___closed__14_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Tactic_invariantDotAlt___closed__15 = (const lean_object*)&l_Lean_Parser_Tactic_invariantDotAlt___closed__15_value;
static const lean_ctor_object l_Lean_Parser_Tactic_invariantDotAlt___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_invariantDotAlt___closed__12_value),((lean_object*)&l_Lean_Parser_Tactic_invariantDotAlt___closed__15_value)}};
static const lean_object* l_Lean_Parser_Tactic_invariantDotAlt___closed__16 = (const lean_object*)&l_Lean_Parser_Tactic_invariantDotAlt___closed__16_value;
static lean_once_cell_t l_Lean_Parser_Tactic_invariantDotAlt___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_invariantDotAlt___closed__17;
static lean_once_cell_t l_Lean_Parser_Tactic_invariantDotAlt___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_invariantDotAlt___closed__18;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_invariantDotAlt;
static const lean_string_object l_Lean_Parser_Tactic_invariantCaseAlt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "invariantCaseAlt"};
static const lean_object* l_Lean_Parser_Tactic_invariantCaseAlt___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_invariantCaseAlt___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_invariantCaseAlt___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_invariantCaseAlt___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_invariantCaseAlt___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_invariantCaseAlt___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_invariantCaseAlt___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_invariantDotAlt___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_invariantCaseAlt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_invariantCaseAlt___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_invariantCaseAlt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(163, 146, 32, 128, 83, 151, 179, 6)}};
static const lean_object* l_Lean_Parser_Tactic_invariantCaseAlt___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_invariantCaseAlt___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_invariantCaseAlt___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "| "};
static const lean_object* l_Lean_Parser_Tactic_invariantCaseAlt___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_invariantCaseAlt___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_invariantCaseAlt___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_invariantCaseAlt___closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_invariantCaseAlt___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_invariantCaseAlt___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_invariantCaseAlt___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_invariantDotAlt___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_invariantCaseAlt___closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_invariantCaseAlt___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_invariantCaseAlt___closed__4_value;
static lean_once_cell_t l_Lean_Parser_Tactic_invariantCaseAlt___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_invariantCaseAlt___closed__5;
static const lean_string_object l_Lean_Parser_Tactic_invariantCaseAlt___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " => "};
static const lean_object* l_Lean_Parser_Tactic_invariantCaseAlt___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_invariantCaseAlt___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_invariantCaseAlt___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_invariantCaseAlt___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_invariantCaseAlt___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_invariantCaseAlt___closed__7_value;
static lean_once_cell_t l_Lean_Parser_Tactic_invariantCaseAlt___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_invariantCaseAlt___closed__8;
static lean_once_cell_t l_Lean_Parser_Tactic_invariantCaseAlt___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_invariantCaseAlt___closed__9;
static lean_once_cell_t l_Lean_Parser_Tactic_invariantCaseAlt___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_invariantCaseAlt___closed__10;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_invariantCaseAlt;
static const lean_string_object l_Lean_Parser_Tactic_invariantsKW___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "invariantsKW"};
static const lean_object* l_Lean_Parser_Tactic_invariantsKW___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_invariantsKW___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_invariantsKW___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_invariantsKW___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_invariantDotAlt___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_invariantsKW___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__0_value),LEAN_SCALAR_PTR_LITERAL(113, 87, 251, 76, 123, 116, 93, 232)}};
static const lean_object* l_Lean_Parser_Tactic_invariantsKW___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_invariantsKW___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "orelse"};
static const lean_object* l_Lean_Parser_Tactic_invariantsKW___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_invariantsKW___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 76, 4, 51, 251, 212, 116, 5)}};
static const lean_object* l_Lean_Parser_Tactic_invariantsKW___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_invariantsKW___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "invariants "};
static const lean_object* l_Lean_Parser_Tactic_invariantsKW___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__4_value;
static const lean_string_object l_Lean_Parser_Tactic_invariantsKW___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "token"};
static const lean_object* l_Lean_Parser_Tactic_invariantsKW___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_invariantsKW___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__5_value),LEAN_SCALAR_PTR_LITERAL(89, 149, 26, 37, 31, 104, 89, 130)}};
static const lean_ctor_object l_Lean_Parser_Tactic_invariantsKW___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__6_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__4_value),LEAN_SCALAR_PTR_LITERAL(252, 45, 21, 37, 250, 87, 14, 102)}};
static const lean_object* l_Lean_Parser_Tactic_invariantsKW___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_invariantsKW___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__4_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_invariantsKW___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_invariantsKW___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__4_value),((lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__7_value)}};
static const lean_object* l_Lean_Parser_Tactic_invariantsKW___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__8_value;
static const lean_string_object l_Lean_Parser_Tactic_invariantsKW___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "invariants\? "};
static const lean_object* l_Lean_Parser_Tactic_invariantsKW___closed__9 = (const lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__9_value;
static const lean_ctor_object l_Lean_Parser_Tactic_invariantsKW___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__5_value),LEAN_SCALAR_PTR_LITERAL(89, 149, 26, 37, 31, 104, 89, 130)}};
static const lean_ctor_object l_Lean_Parser_Tactic_invariantsKW___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__10_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__9_value),LEAN_SCALAR_PTR_LITERAL(241, 40, 134, 186, 103, 193, 43, 220)}};
static const lean_object* l_Lean_Parser_Tactic_invariantsKW___closed__10 = (const lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__10_value;
static const lean_ctor_object l_Lean_Parser_Tactic_invariantsKW___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__9_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_invariantsKW___closed__11 = (const lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__11_value;
static const lean_ctor_object l_Lean_Parser_Tactic_invariantsKW___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__9_value),((lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__10_value),((lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__11_value)}};
static const lean_object* l_Lean_Parser_Tactic_invariantsKW___closed__12 = (const lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__12_value;
static const lean_ctor_object l_Lean_Parser_Tactic_invariantsKW___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__12_value)}};
static const lean_object* l_Lean_Parser_Tactic_invariantsKW___closed__13 = (const lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__13_value;
static const lean_ctor_object l_Lean_Parser_Tactic_invariantsKW___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__0_value),((lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__1_value),((lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__13_value)}};
static const lean_object* l_Lean_Parser_Tactic_invariantsKW___closed__14 = (const lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__14_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_invariantsKW = (const lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__14_value;
static const lean_string_object l_Lean_Parser_Tactic_invariantAlts___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "invariantAlts"};
static const lean_object* l_Lean_Parser_Tactic_invariantAlts___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_invariantAlts___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_invariantAlts___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_invariantAlts___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_invariantAlts___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_invariantAlts___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_invariantAlts___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_invariantDotAlt___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_invariantAlts___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_invariantAlts___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_invariantAlts___closed__0_value),LEAN_SCALAR_PTR_LITERAL(30, 41, 254, 250, 50, 69, 99, 10)}};
static const lean_object* l_Lean_Parser_Tactic_invariantAlts___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_invariantAlts___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_invariantAlts___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "withPosition"};
static const lean_object* l_Lean_Parser_Tactic_invariantAlts___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_invariantAlts___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_invariantAlts___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_invariantAlts___closed__2_value),LEAN_SCALAR_PTR_LITERAL(246, 171, 180, 145, 132, 143, 108, 238)}};
static const lean_object* l_Lean_Parser_Tactic_invariantAlts___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_invariantAlts___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_invariantAlts___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "many"};
static const lean_object* l_Lean_Parser_Tactic_invariantAlts___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_invariantAlts___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_invariantAlts___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_invariantAlts___closed__4_value),LEAN_SCALAR_PTR_LITERAL(41, 35, 40, 86, 189, 97, 244, 31)}};
static const lean_object* l_Lean_Parser_Tactic_invariantAlts___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_invariantAlts___closed__5_value;
static lean_once_cell_t l_Lean_Parser_Tactic_invariantAlts___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_invariantAlts___closed__6;
static lean_once_cell_t l_Lean_Parser_Tactic_invariantAlts___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_invariantAlts___closed__7;
static lean_once_cell_t l_Lean_Parser_Tactic_invariantAlts___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_invariantAlts___closed__8;
static lean_once_cell_t l_Lean_Parser_Tactic_invariantAlts___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_invariantAlts___closed__9;
static lean_once_cell_t l_Lean_Parser_Tactic_invariantAlts___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_invariantAlts___closed__10;
static lean_once_cell_t l_Lean_Parser_Tactic_invariantAlts___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_invariantAlts___closed__11;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_invariantAlts;
static const lean_string_object l_Lean_Parser_Tactic_frameAlt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "frameAlt"};
static const lean_object* l_Lean_Parser_Tactic_frameAlt___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_frameAlt___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_frameAlt___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_frameAlt___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_frameAlt___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_frameAlt___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_frameAlt___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_invariantDotAlt___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_frameAlt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_frameAlt___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_frameAlt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(199, 154, 201, 239, 176, 247, 171, 168)}};
static const lean_object* l_Lean_Parser_Tactic_frameAlt___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_frameAlt___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_frameAlt___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Parser_Tactic_frameAlt___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_frameAlt___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_frameAlt___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_frameAlt___closed__2_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Parser_Tactic_frameAlt___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_frameAlt___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_frameAlt___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_frameAlt___closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_frameAlt___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_frameAlt___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_frameAlt___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_invariantCaseAlt___closed__4_value),((lean_object*)&l_Lean_Parser_Tactic_frameAlt___closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_frameAlt___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_frameAlt___closed__5_value;
static const lean_string_object l_Lean_Parser_Tactic_frameAlt___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "colGt"};
static const lean_object* l_Lean_Parser_Tactic_frameAlt___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_frameAlt___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_frameAlt___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_frameAlt___closed__6_value),LEAN_SCALAR_PTR_LITERAL(185, 236, 32, 153, 169, 213, 53, 244)}};
static const lean_object* l_Lean_Parser_Tactic_frameAlt___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_frameAlt___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_frameAlt___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_frameAlt___closed__7_value)}};
static const lean_object* l_Lean_Parser_Tactic_frameAlt___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_frameAlt___closed__8_value;
static const lean_ctor_object l_Lean_Parser_Tactic_frameAlt___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Attr_spec___closed__12_value),((lean_object*)&l_Lean_Parser_Tactic_frameAlt___closed__8_value)}};
static const lean_object* l_Lean_Parser_Tactic_frameAlt___closed__9 = (const lean_object*)&l_Lean_Parser_Tactic_frameAlt___closed__9_value;
static lean_once_cell_t l_Lean_Parser_Tactic_frameAlt___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_frameAlt___closed__10;
static lean_once_cell_t l_Lean_Parser_Tactic_frameAlt___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_frameAlt___closed__11;
static lean_once_cell_t l_Lean_Parser_Tactic_frameAlt___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_frameAlt___closed__12;
static lean_once_cell_t l_Lean_Parser_Tactic_frameAlt___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_frameAlt___closed__13;
static lean_once_cell_t l_Lean_Parser_Tactic_frameAlt___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_frameAlt___closed__14;
static lean_once_cell_t l_Lean_Parser_Tactic_frameAlt___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_frameAlt___closed__15;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_frameAlt;
static const lean_string_object l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__0_value;
static const lean_string_object l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "quot"};
static const lean_object* l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__2_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__2_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__2_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(145, 163, 173, 41, 168, 168, 65, 81)}};
static const lean_object* l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__2_value;
static const lean_string_object l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "vcgenDischarge"};
static const lean_object* l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__3_value),LEAN_SCALAR_PTR_LITERAL(86, 220, 68, 107, 35, 129, 181, 68)}};
static const lean_ctor_object l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__4_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(80, 250, 109, 29, 148, 28, 116, 141)}};
static const lean_object* l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__4_value;
static const lean_string_object l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "`(vcgenDischarge| "};
static const lean_object* l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__3_value),LEAN_SCALAR_PTR_LITERAL(86, 220, 68, 107, 35, 129, 181, 68)}};
static const lean_object* l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__7_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__8_value;
static const lean_string_object l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__9 = (const lean_object*)&l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__9_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__9_value)}};
static const lean_object* l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__10 = (const lean_object*)&l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__10_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__10_value)}};
static const lean_object* l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__11 = (const lean_object*)&l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__11_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__11_value)}};
static const lean_object* l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__12 = (const lean_object*)&l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__12_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__4_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__12_value)}};
static const lean_object* l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__13 = (const lean_object*)&l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__13_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__2_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__13_value)}};
static const lean_object* l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__14 = (const lean_object*)&l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__14_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_vcgenDischarge_quot = (const lean_object*)&l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__14_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Category_vcgenDischarge;
static const lean_string_object l_Lean_Parser_Tactic_vcgenDischargeGrind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "vcgenDischargeGrind"};
static const lean_object* l_Lean_Parser_Tactic_vcgenDischargeGrind___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_vcgenDischargeGrind___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcgenDischargeGrind___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_vcgenDischargeGrind___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_vcgenDischargeGrind___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_vcgenDischargeGrind___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_vcgenDischargeGrind___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_invariantDotAlt___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_vcgenDischargeGrind___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_vcgenDischargeGrind___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_vcgenDischargeGrind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(7, 199, 17, 154, 227, 108, 8, 170)}};
static const lean_object* l_Lean_Parser_Tactic_vcgenDischargeGrind___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_vcgenDischargeGrind___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_vcgenDischargeGrind___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l_Lean_Parser_Tactic_vcgenDischargeGrind___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_vcgenDischargeGrind___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcgenDischargeGrind___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_vcgenDischargeGrind___closed__2_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_object* l_Lean_Parser_Tactic_vcgenDischargeGrind___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_vcgenDischargeGrind___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcgenDischargeGrind___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_vcgenDischargeGrind___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Tactic_vcgenDischargeGrind___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_vcgenDischargeGrind___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcgenDischargeGrind___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_vcgenDischargeGrind___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_vcgenDischargeGrind___closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_vcgenDischargeGrind___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_vcgenDischargeGrind___closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_vcgenDischargeGrind = (const lean_object*)&l_Lean_Parser_Tactic_vcgenDischargeGrind___closed__5_value;
static const lean_string_object l_Lean_Parser_Tactic_vcgenDischargeTactic___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "vcgenDischargeTactic"};
static const lean_object* l_Lean_Parser_Tactic_vcgenDischargeTactic___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_vcgenDischargeTactic___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcgenDischargeTactic___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_vcgenDischargeTactic___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_vcgenDischargeTactic___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_vcgenDischargeTactic___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_vcgenDischargeTactic___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_invariantDotAlt___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_vcgenDischargeTactic___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_vcgenDischargeTactic___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_vcgenDischargeTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(249, 78, 68, 156, 106, 197, 226, 93)}};
static const lean_object* l_Lean_Parser_Tactic_vcgenDischargeTactic___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_vcgenDischargeTactic___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_vcgenDischargeTactic___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "tactic"};
static const lean_object* l_Lean_Parser_Tactic_vcgenDischargeTactic___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_vcgenDischargeTactic___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcgenDischargeTactic___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_vcgenDischargeTactic___closed__2_value),LEAN_SCALAR_PTR_LITERAL(99, 76, 33, 121, 85, 143, 17, 224)}};
static const lean_object* l_Lean_Parser_Tactic_vcgenDischargeTactic___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_vcgenDischargeTactic___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcgenDischargeTactic___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_vcgenDischargeTactic___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Tactic_vcgenDischargeTactic___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_vcgenDischargeTactic___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcgenDischargeTactic___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_vcgenDischargeTactic___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_vcgenDischargeTactic___closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_vcgenDischargeTactic___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_vcgenDischargeTactic___closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_vcgenDischargeTactic = (const lean_object*)&l_Lean_Parser_Tactic_vcgenDischargeTactic___closed__5_value;
static const lean_string_object l_Lean_Parser_Tactic_vcgen___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "vcgen"};
static const lean_object* l_Lean_Parser_Tactic_vcgen___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcgen___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_vcgen___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_vcgen___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_invariantDotAlt___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_vcgen___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 196, 10, 243, 239, 189, 222, 13)}};
static const lean_object* l_Lean_Parser_Tactic_vcgen___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcgen___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_vcgen___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__2_value;
static lean_once_cell_t l_Lean_Parser_Tactic_vcgen___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_vcgen___closed__3;
static const lean_string_object l_Lean_Parser_Tactic_vcgen___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " ["};
static const lean_object* l_Lean_Parser_Tactic_vcgen___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcgen___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_vcgen___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__5_value;
static const lean_string_object l_Lean_Parser_Tactic_vcgen___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "withoutPosition"};
static const lean_object* l_Lean_Parser_Tactic_vcgen___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcgen___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__6_value),LEAN_SCALAR_PTR_LITERAL(69, 6, 27, 142, 141, 165, 41, 16)}};
static const lean_object* l_Lean_Parser_Tactic_vcgen___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__7_value;
static lean_once_cell_t l_Lean_Parser_Tactic_vcgen___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_vcgen___closed__8;
static lean_once_cell_t l_Lean_Parser_Tactic_vcgen___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_vcgen___closed__9;
static const lean_string_object l_Lean_Parser_Tactic_vcgen___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_Parser_Tactic_vcgen___closed__10 = (const lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__10_value;
static const lean_string_object l_Lean_Parser_Tactic_vcgen___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_Lean_Parser_Tactic_vcgen___closed__11 = (const lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__11_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcgen___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__11_value)}};
static const lean_object* l_Lean_Parser_Tactic_vcgen___closed__12 = (const lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__12_value;
static lean_once_cell_t l_Lean_Parser_Tactic_vcgen___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_vcgen___closed__13;
static lean_once_cell_t l_Lean_Parser_Tactic_vcgen___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_vcgen___closed__14;
static lean_once_cell_t l_Lean_Parser_Tactic_vcgen___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_vcgen___closed__15;
static const lean_string_object l_Lean_Parser_Tactic_vcgen___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "] "};
static const lean_object* l_Lean_Parser_Tactic_vcgen___closed__16 = (const lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__16_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcgen___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__16_value)}};
static const lean_object* l_Lean_Parser_Tactic_vcgen___closed__17 = (const lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__17_value;
static lean_once_cell_t l_Lean_Parser_Tactic_vcgen___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_vcgen___closed__18;
static lean_once_cell_t l_Lean_Parser_Tactic_vcgen___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_vcgen___closed__19;
static lean_once_cell_t l_Lean_Parser_Tactic_vcgen___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_vcgen___closed__20;
static const lean_string_object l_Lean_Parser_Tactic_vcgen___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " until "};
static const lean_object* l_Lean_Parser_Tactic_vcgen___closed__21 = (const lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__21_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcgen___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__21_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_vcgen___closed__22 = (const lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__22_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcgen___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__22_value),((lean_object*)&l_Lean_Parser_Tactic_invariantDotAlt___closed__15_value)}};
static const lean_object* l_Lean_Parser_Tactic_vcgen___closed__23 = (const lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__23_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcgen___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__9_value),((lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__23_value)}};
static const lean_object* l_Lean_Parser_Tactic_vcgen___closed__24 = (const lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__24_value;
static lean_once_cell_t l_Lean_Parser_Tactic_vcgen___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_vcgen___closed__25;
static const lean_string_object l_Lean_Parser_Tactic_vcgen___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = " frames "};
static const lean_object* l_Lean_Parser_Tactic_vcgen___closed__26 = (const lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__26_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcgen___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__26_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_vcgen___closed__27 = (const lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__27_value;
static const lean_string_object l_Lean_Parser_Tactic_vcgen___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "many1"};
static const lean_object* l_Lean_Parser_Tactic_vcgen___closed__28 = (const lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__28_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcgen___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__28_value),LEAN_SCALAR_PTR_LITERAL(55, 136, 52, 6, 12, 19, 78, 239)}};
static const lean_object* l_Lean_Parser_Tactic_vcgen___closed__29 = (const lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__29_value;
static lean_once_cell_t l_Lean_Parser_Tactic_vcgen___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_vcgen___closed__30;
static lean_once_cell_t l_Lean_Parser_Tactic_vcgen___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_vcgen___closed__31;
static lean_once_cell_t l_Lean_Parser_Tactic_vcgen___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_vcgen___closed__32;
static lean_once_cell_t l_Lean_Parser_Tactic_vcgen___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_vcgen___closed__33;
static lean_once_cell_t l_Lean_Parser_Tactic_vcgen___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_vcgen___closed__34;
static lean_once_cell_t l_Lean_Parser_Tactic_vcgen___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_vcgen___closed__35;
static lean_once_cell_t l_Lean_Parser_Tactic_vcgen___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_vcgen___closed__36;
static lean_once_cell_t l_Lean_Parser_Tactic_vcgen___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_vcgen___closed__37;
static const lean_string_object l_Lean_Parser_Tactic_vcgen___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = " simplifying_assumptions"};
static const lean_object* l_Lean_Parser_Tactic_vcgen___closed__38 = (const lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__38_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcgen___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__38_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_vcgen___closed__39 = (const lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__39_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcgen___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_frameAlt___closed__9_value),((lean_object*)&l_Lean_Parser_Tactic_frameAlt___closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_vcgen___closed__40 = (const lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__40_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcgen___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__9_value),((lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__40_value)}};
static const lean_object* l_Lean_Parser_Tactic_vcgen___closed__41 = (const lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__41_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcgen___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__39_value),((lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__41_value)}};
static const lean_object* l_Lean_Parser_Tactic_vcgen___closed__42 = (const lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__42_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcgen___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 10}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_frameAlt___closed__4_value),((lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__10_value),((lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__12_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_vcgen___closed__43 = (const lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__43_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcgen___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__5_value),((lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__43_value)}};
static const lean_object* l_Lean_Parser_Tactic_vcgen___closed__44 = (const lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__44_value;
static const lean_string_object l_Lean_Parser_Tactic_vcgen___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_Parser_Tactic_vcgen___closed__45 = (const lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__45_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcgen___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__45_value)}};
static const lean_object* l_Lean_Parser_Tactic_vcgen___closed__46 = (const lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__46_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcgen___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__44_value),((lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__46_value)}};
static const lean_object* l_Lean_Parser_Tactic_vcgen___closed__47 = (const lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__47_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcgen___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__9_value),((lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__47_value)}};
static const lean_object* l_Lean_Parser_Tactic_vcgen___closed__48 = (const lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__48_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcgen___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__42_value),((lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__48_value)}};
static const lean_object* l_Lean_Parser_Tactic_vcgen___closed__49 = (const lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__49_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcgen___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__9_value),((lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__49_value)}};
static const lean_object* l_Lean_Parser_Tactic_vcgen___closed__50 = (const lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__50_value;
static lean_once_cell_t l_Lean_Parser_Tactic_vcgen___closed__51_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_vcgen___closed__51;
static const lean_string_object l_Lean_Parser_Tactic_vcgen___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = " with "};
static const lean_object* l_Lean_Parser_Tactic_vcgen___closed__52 = (const lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__52_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcgen___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__52_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_vcgen___closed__53 = (const lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__53_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcgen___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__53_value),((lean_object*)&l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__8_value)}};
static const lean_object* l_Lean_Parser_Tactic_vcgen___closed__54 = (const lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__54_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcgen___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__9_value),((lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__54_value)}};
static const lean_object* l_Lean_Parser_Tactic_vcgen___closed__55 = (const lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__55_value;
static lean_once_cell_t l_Lean_Parser_Tactic_vcgen___closed__56_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_vcgen___closed__56;
static lean_once_cell_t l_Lean_Parser_Tactic_vcgen___closed__57_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_vcgen___closed__57;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_vcgen;
static const lean_string_object l_Lean_Parser_Tactic_Grind_vcgen___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l_Lean_Parser_Tactic_Grind_vcgen___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_vcgen___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_vcgen___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_vcgen___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_vcgen___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_vcgen___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_vcgen___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_invariantDotAlt___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_vcgen___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_vcgen___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_vcgen___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_vcgen___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_vcgen___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__0_value),LEAN_SCALAR_PTR_LITERAL(113, 229, 87, 15, 155, 212, 124, 96)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_vcgen___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_vcgen___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Tactic_Grind_vcgen___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Grind_vcgen___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind_vcgen;
static lean_object* _init_l_Lean_Parser_Tactic_invariantDotAlt___closed__9(void){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_64_ = l_Lean_cdotTk;
v___x_65_ = ((lean_object*)(l_Lean_Parser_Tactic_invariantDotAlt___closed__8));
v___x_66_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_67_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_67_, 0, v___x_66_);
lean_ctor_set(v___x_67_, 1, v___x_65_);
lean_ctor_set(v___x_67_, 2, v___x_64_);
return v___x_67_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_invariantDotAlt___closed__17(void){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_83_ = ((lean_object*)(l_Lean_Parser_Tactic_invariantDotAlt___closed__16));
v___x_84_ = lean_obj_once(&l_Lean_Parser_Tactic_invariantDotAlt___closed__9, &l_Lean_Parser_Tactic_invariantDotAlt___closed__9_once, _init_l_Lean_Parser_Tactic_invariantDotAlt___closed__9);
v___x_85_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_86_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_86_, 0, v___x_85_);
lean_ctor_set(v___x_86_, 1, v___x_84_);
lean_ctor_set(v___x_86_, 2, v___x_83_);
return v___x_86_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_invariantDotAlt___closed__18(void){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_87_ = lean_obj_once(&l_Lean_Parser_Tactic_invariantDotAlt___closed__17, &l_Lean_Parser_Tactic_invariantDotAlt___closed__17_once, _init_l_Lean_Parser_Tactic_invariantDotAlt___closed__17);
v___x_88_ = ((lean_object*)(l_Lean_Parser_Tactic_invariantDotAlt___closed__2));
v___x_89_ = ((lean_object*)(l_Lean_Parser_Tactic_invariantDotAlt___closed__0));
v___x_90_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_90_, 0, v___x_89_);
lean_ctor_set(v___x_90_, 1, v___x_88_);
lean_ctor_set(v___x_90_, 2, v___x_87_);
return v___x_90_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_invariantDotAlt(void){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = lean_obj_once(&l_Lean_Parser_Tactic_invariantDotAlt___closed__18, &l_Lean_Parser_Tactic_invariantDotAlt___closed__18_once, _init_l_Lean_Parser_Tactic_invariantDotAlt___closed__18);
return v___x_91_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_invariantCaseAlt___closed__5(void){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_105_ = l_Lean_Parser_Tactic_caseArg;
v___x_106_ = ((lean_object*)(l_Lean_Parser_Tactic_invariantCaseAlt___closed__4));
v___x_107_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_108_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_108_, 0, v___x_107_);
lean_ctor_set(v___x_108_, 1, v___x_106_);
lean_ctor_set(v___x_108_, 2, v___x_105_);
return v___x_108_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_invariantCaseAlt___closed__8(void){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_112_ = ((lean_object*)(l_Lean_Parser_Tactic_invariantCaseAlt___closed__7));
v___x_113_ = lean_obj_once(&l_Lean_Parser_Tactic_invariantCaseAlt___closed__5, &l_Lean_Parser_Tactic_invariantCaseAlt___closed__5_once, _init_l_Lean_Parser_Tactic_invariantCaseAlt___closed__5);
v___x_114_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_115_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_115_, 0, v___x_114_);
lean_ctor_set(v___x_115_, 1, v___x_113_);
lean_ctor_set(v___x_115_, 2, v___x_112_);
return v___x_115_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_invariantCaseAlt___closed__9(void){
_start:
{
lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_116_ = ((lean_object*)(l_Lean_Parser_Tactic_invariantDotAlt___closed__16));
v___x_117_ = lean_obj_once(&l_Lean_Parser_Tactic_invariantCaseAlt___closed__8, &l_Lean_Parser_Tactic_invariantCaseAlt___closed__8_once, _init_l_Lean_Parser_Tactic_invariantCaseAlt___closed__8);
v___x_118_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_119_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_119_, 0, v___x_118_);
lean_ctor_set(v___x_119_, 1, v___x_117_);
lean_ctor_set(v___x_119_, 2, v___x_116_);
return v___x_119_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_invariantCaseAlt___closed__10(void){
_start:
{
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_120_ = lean_obj_once(&l_Lean_Parser_Tactic_invariantCaseAlt___closed__9, &l_Lean_Parser_Tactic_invariantCaseAlt___closed__9_once, _init_l_Lean_Parser_Tactic_invariantCaseAlt___closed__9);
v___x_121_ = ((lean_object*)(l_Lean_Parser_Tactic_invariantCaseAlt___closed__1));
v___x_122_ = ((lean_object*)(l_Lean_Parser_Tactic_invariantCaseAlt___closed__0));
v___x_123_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_123_, 0, v___x_122_);
lean_ctor_set(v___x_123_, 1, v___x_121_);
lean_ctor_set(v___x_123_, 2, v___x_120_);
return v___x_123_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_invariantCaseAlt(void){
_start:
{
lean_object* v___x_124_; 
v___x_124_ = lean_obj_once(&l_Lean_Parser_Tactic_invariantCaseAlt___closed__10, &l_Lean_Parser_Tactic_invariantCaseAlt___closed__10_once, _init_l_Lean_Parser_Tactic_invariantCaseAlt___closed__10);
return v___x_124_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_invariantAlts___closed__6(void){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_178_ = l_Lean_Parser_Tactic_invariantCaseAlt;
v___x_179_ = l_Lean_Parser_Tactic_invariantDotAlt;
v___x_180_ = ((lean_object*)(l_Lean_Parser_Tactic_invariantsKW___closed__3));
v___x_181_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_181_, 0, v___x_180_);
lean_ctor_set(v___x_181_, 1, v___x_179_);
lean_ctor_set(v___x_181_, 2, v___x_178_);
return v___x_181_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_invariantAlts___closed__7(void){
_start:
{
lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_182_ = lean_obj_once(&l_Lean_Parser_Tactic_invariantAlts___closed__6, &l_Lean_Parser_Tactic_invariantAlts___closed__6_once, _init_l_Lean_Parser_Tactic_invariantAlts___closed__6);
v___x_183_ = ((lean_object*)(l_Lean_Parser_Tactic_invariantDotAlt___closed__12));
v___x_184_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_185_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_185_, 0, v___x_184_);
lean_ctor_set(v___x_185_, 1, v___x_183_);
lean_ctor_set(v___x_185_, 2, v___x_182_);
return v___x_185_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_invariantAlts___closed__8(void){
_start:
{
lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_186_ = lean_obj_once(&l_Lean_Parser_Tactic_invariantAlts___closed__7, &l_Lean_Parser_Tactic_invariantAlts___closed__7_once, _init_l_Lean_Parser_Tactic_invariantAlts___closed__7);
v___x_187_ = ((lean_object*)(l_Lean_Parser_Tactic_invariantAlts___closed__5));
v___x_188_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_188_, 0, v___x_187_);
lean_ctor_set(v___x_188_, 1, v___x_186_);
return v___x_188_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_invariantAlts___closed__9(void){
_start:
{
lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_189_ = lean_obj_once(&l_Lean_Parser_Tactic_invariantAlts___closed__8, &l_Lean_Parser_Tactic_invariantAlts___closed__8_once, _init_l_Lean_Parser_Tactic_invariantAlts___closed__8);
v___x_190_ = ((lean_object*)(l_Lean_Parser_Tactic_invariantAlts___closed__3));
v___x_191_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_191_, 0, v___x_190_);
lean_ctor_set(v___x_191_, 1, v___x_189_);
return v___x_191_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_invariantAlts___closed__10(void){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_192_ = lean_obj_once(&l_Lean_Parser_Tactic_invariantAlts___closed__9, &l_Lean_Parser_Tactic_invariantAlts___closed__9_once, _init_l_Lean_Parser_Tactic_invariantAlts___closed__9);
v___x_193_ = ((lean_object*)(l_Lean_Parser_Tactic_invariantsKW));
v___x_194_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_195_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_195_, 0, v___x_194_);
lean_ctor_set(v___x_195_, 1, v___x_193_);
lean_ctor_set(v___x_195_, 2, v___x_192_);
return v___x_195_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_invariantAlts___closed__11(void){
_start:
{
lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_196_ = lean_obj_once(&l_Lean_Parser_Tactic_invariantAlts___closed__10, &l_Lean_Parser_Tactic_invariantAlts___closed__10_once, _init_l_Lean_Parser_Tactic_invariantAlts___closed__10);
v___x_197_ = ((lean_object*)(l_Lean_Parser_Tactic_invariantAlts___closed__1));
v___x_198_ = ((lean_object*)(l_Lean_Parser_Tactic_invariantAlts___closed__0));
v___x_199_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_199_, 0, v___x_198_);
lean_ctor_set(v___x_199_, 1, v___x_197_);
lean_ctor_set(v___x_199_, 2, v___x_196_);
return v___x_199_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_invariantAlts(void){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = lean_obj_once(&l_Lean_Parser_Tactic_invariantAlts___closed__11, &l_Lean_Parser_Tactic_invariantAlts___closed__11_once, _init_l_Lean_Parser_Tactic_invariantAlts___closed__11);
return v___x_200_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_frameAlt___closed__10(void){
_start:
{
lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_225_ = l_Lean_binderIdent;
v___x_226_ = ((lean_object*)(l_Lean_Parser_Tactic_frameAlt___closed__9));
v___x_227_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_228_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_228_, 0, v___x_227_);
lean_ctor_set(v___x_228_, 1, v___x_226_);
lean_ctor_set(v___x_228_, 2, v___x_225_);
return v___x_228_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_frameAlt___closed__11(void){
_start:
{
lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_229_ = lean_obj_once(&l_Lean_Parser_Tactic_frameAlt___closed__10, &l_Lean_Parser_Tactic_frameAlt___closed__10_once, _init_l_Lean_Parser_Tactic_frameAlt___closed__10);
v___x_230_ = ((lean_object*)(l_Lean_Parser_Tactic_invariantAlts___closed__5));
v___x_231_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_231_, 0, v___x_230_);
lean_ctor_set(v___x_231_, 1, v___x_229_);
return v___x_231_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_frameAlt___closed__12(void){
_start:
{
lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_232_ = lean_obj_once(&l_Lean_Parser_Tactic_frameAlt___closed__11, &l_Lean_Parser_Tactic_frameAlt___closed__11_once, _init_l_Lean_Parser_Tactic_frameAlt___closed__11);
v___x_233_ = ((lean_object*)(l_Lean_Parser_Tactic_frameAlt___closed__5));
v___x_234_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_235_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_235_, 0, v___x_234_);
lean_ctor_set(v___x_235_, 1, v___x_233_);
lean_ctor_set(v___x_235_, 2, v___x_232_);
return v___x_235_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_frameAlt___closed__13(void){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_236_ = ((lean_object*)(l_Lean_Parser_Tactic_invariantCaseAlt___closed__7));
v___x_237_ = lean_obj_once(&l_Lean_Parser_Tactic_frameAlt___closed__12, &l_Lean_Parser_Tactic_frameAlt___closed__12_once, _init_l_Lean_Parser_Tactic_frameAlt___closed__12);
v___x_238_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_239_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_239_, 0, v___x_238_);
lean_ctor_set(v___x_239_, 1, v___x_237_);
lean_ctor_set(v___x_239_, 2, v___x_236_);
return v___x_239_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_frameAlt___closed__14(void){
_start:
{
lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_240_ = ((lean_object*)(l_Lean_Parser_Tactic_invariantDotAlt___closed__16));
v___x_241_ = lean_obj_once(&l_Lean_Parser_Tactic_frameAlt___closed__13, &l_Lean_Parser_Tactic_frameAlt___closed__13_once, _init_l_Lean_Parser_Tactic_frameAlt___closed__13);
v___x_242_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_243_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_243_, 0, v___x_242_);
lean_ctor_set(v___x_243_, 1, v___x_241_);
lean_ctor_set(v___x_243_, 2, v___x_240_);
return v___x_243_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_frameAlt___closed__15(void){
_start:
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_244_ = lean_obj_once(&l_Lean_Parser_Tactic_frameAlt___closed__14, &l_Lean_Parser_Tactic_frameAlt___closed__14_once, _init_l_Lean_Parser_Tactic_frameAlt___closed__14);
v___x_245_ = ((lean_object*)(l_Lean_Parser_Tactic_frameAlt___closed__1));
v___x_246_ = ((lean_object*)(l_Lean_Parser_Tactic_frameAlt___closed__0));
v___x_247_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_247_, 0, v___x_246_);
lean_ctor_set(v___x_247_, 1, v___x_245_);
lean_ctor_set(v___x_247_, 2, v___x_244_);
return v___x_247_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_frameAlt(void){
_start:
{
lean_object* v___x_248_; 
v___x_248_ = lean_obj_once(&l_Lean_Parser_Tactic_frameAlt___closed__15, &l_Lean_Parser_Tactic_frameAlt___closed__15_once, _init_l_Lean_Parser_Tactic_frameAlt___closed__15);
return v___x_248_;
}
}
static lean_object* _init_l_Lean_Parser_Category_vcgenDischarge(void){
_start:
{
lean_object* v___x_288_; 
v___x_288_ = lean_box(0);
return v___x_288_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_vcgen___closed__3(void){
_start:
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_332_ = l_Lean_Parser_Tactic_optConfig;
v___x_333_ = ((lean_object*)(l_Lean_Parser_Tactic_vcgen___closed__2));
v___x_334_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_335_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
lean_ctor_set(v___x_335_, 1, v___x_333_);
lean_ctor_set(v___x_335_, 2, v___x_332_);
return v___x_335_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_vcgen___closed__8(void){
_start:
{
lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_342_ = l_Lean_Parser_Tactic_simpLemma;
v___x_343_ = l_Lean_Parser_Tactic_simpErase;
v___x_344_ = ((lean_object*)(l_Lean_Parser_Tactic_invariantsKW___closed__3));
v___x_345_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_345_, 0, v___x_344_);
lean_ctor_set(v___x_345_, 1, v___x_343_);
lean_ctor_set(v___x_345_, 2, v___x_342_);
return v___x_345_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_vcgen___closed__9(void){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_346_ = lean_obj_once(&l_Lean_Parser_Tactic_vcgen___closed__8, &l_Lean_Parser_Tactic_vcgen___closed__8_once, _init_l_Lean_Parser_Tactic_vcgen___closed__8);
v___x_347_ = l_Lean_Parser_Tactic_simpStar;
v___x_348_ = ((lean_object*)(l_Lean_Parser_Tactic_invariantsKW___closed__3));
v___x_349_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_349_, 0, v___x_348_);
lean_ctor_set(v___x_349_, 1, v___x_347_);
lean_ctor_set(v___x_349_, 2, v___x_346_);
return v___x_349_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_vcgen___closed__13(void){
_start:
{
uint8_t v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_354_ = 1;
v___x_355_ = ((lean_object*)(l_Lean_Parser_Tactic_vcgen___closed__12));
v___x_356_ = ((lean_object*)(l_Lean_Parser_Tactic_vcgen___closed__10));
v___x_357_ = lean_obj_once(&l_Lean_Parser_Tactic_vcgen___closed__9, &l_Lean_Parser_Tactic_vcgen___closed__9_once, _init_l_Lean_Parser_Tactic_vcgen___closed__9);
v___x_358_ = lean_alloc_ctor(10, 3, 1);
lean_ctor_set(v___x_358_, 0, v___x_357_);
lean_ctor_set(v___x_358_, 1, v___x_356_);
lean_ctor_set(v___x_358_, 2, v___x_355_);
lean_ctor_set_uint8(v___x_358_, sizeof(void*)*3, v___x_354_);
return v___x_358_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_vcgen___closed__14(void){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_359_ = lean_obj_once(&l_Lean_Parser_Tactic_vcgen___closed__13, &l_Lean_Parser_Tactic_vcgen___closed__13_once, _init_l_Lean_Parser_Tactic_vcgen___closed__13);
v___x_360_ = ((lean_object*)(l_Lean_Parser_Tactic_vcgen___closed__7));
v___x_361_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_361_, 0, v___x_360_);
lean_ctor_set(v___x_361_, 1, v___x_359_);
return v___x_361_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_vcgen___closed__15(void){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_362_ = lean_obj_once(&l_Lean_Parser_Tactic_vcgen___closed__14, &l_Lean_Parser_Tactic_vcgen___closed__14_once, _init_l_Lean_Parser_Tactic_vcgen___closed__14);
v___x_363_ = ((lean_object*)(l_Lean_Parser_Tactic_vcgen___closed__5));
v___x_364_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_365_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_365_, 0, v___x_364_);
lean_ctor_set(v___x_365_, 1, v___x_363_);
lean_ctor_set(v___x_365_, 2, v___x_362_);
return v___x_365_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_vcgen___closed__18(void){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_369_ = ((lean_object*)(l_Lean_Parser_Tactic_vcgen___closed__17));
v___x_370_ = lean_obj_once(&l_Lean_Parser_Tactic_vcgen___closed__15, &l_Lean_Parser_Tactic_vcgen___closed__15_once, _init_l_Lean_Parser_Tactic_vcgen___closed__15);
v___x_371_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_372_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_372_, 0, v___x_371_);
lean_ctor_set(v___x_372_, 1, v___x_370_);
lean_ctor_set(v___x_372_, 2, v___x_369_);
return v___x_372_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_vcgen___closed__19(void){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_373_ = lean_obj_once(&l_Lean_Parser_Tactic_vcgen___closed__18, &l_Lean_Parser_Tactic_vcgen___closed__18_once, _init_l_Lean_Parser_Tactic_vcgen___closed__18);
v___x_374_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__9));
v___x_375_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_375_, 0, v___x_374_);
lean_ctor_set(v___x_375_, 1, v___x_373_);
return v___x_375_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_vcgen___closed__20(void){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_376_ = lean_obj_once(&l_Lean_Parser_Tactic_vcgen___closed__19, &l_Lean_Parser_Tactic_vcgen___closed__19_once, _init_l_Lean_Parser_Tactic_vcgen___closed__19);
v___x_377_ = lean_obj_once(&l_Lean_Parser_Tactic_vcgen___closed__3, &l_Lean_Parser_Tactic_vcgen___closed__3_once, _init_l_Lean_Parser_Tactic_vcgen___closed__3);
v___x_378_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_379_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_379_, 0, v___x_378_);
lean_ctor_set(v___x_379_, 1, v___x_377_);
lean_ctor_set(v___x_379_, 2, v___x_376_);
return v___x_379_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_vcgen___closed__25(void){
_start:
{
lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_391_ = ((lean_object*)(l_Lean_Parser_Tactic_vcgen___closed__24));
v___x_392_ = lean_obj_once(&l_Lean_Parser_Tactic_vcgen___closed__20, &l_Lean_Parser_Tactic_vcgen___closed__20_once, _init_l_Lean_Parser_Tactic_vcgen___closed__20);
v___x_393_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_394_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_394_, 0, v___x_393_);
lean_ctor_set(v___x_394_, 1, v___x_392_);
lean_ctor_set(v___x_394_, 2, v___x_391_);
return v___x_394_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_vcgen___closed__30(void){
_start:
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_402_ = l_Lean_Parser_Tactic_frameAlt;
v___x_403_ = ((lean_object*)(l_Lean_Parser_Tactic_invariantDotAlt___closed__12));
v___x_404_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_405_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_405_, 0, v___x_404_);
lean_ctor_set(v___x_405_, 1, v___x_403_);
lean_ctor_set(v___x_405_, 2, v___x_402_);
return v___x_405_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_vcgen___closed__31(void){
_start:
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_406_ = lean_obj_once(&l_Lean_Parser_Tactic_vcgen___closed__30, &l_Lean_Parser_Tactic_vcgen___closed__30_once, _init_l_Lean_Parser_Tactic_vcgen___closed__30);
v___x_407_ = ((lean_object*)(l_Lean_Parser_Tactic_vcgen___closed__29));
v___x_408_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_408_, 0, v___x_407_);
lean_ctor_set(v___x_408_, 1, v___x_406_);
return v___x_408_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_vcgen___closed__32(void){
_start:
{
lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_409_ = lean_obj_once(&l_Lean_Parser_Tactic_vcgen___closed__31, &l_Lean_Parser_Tactic_vcgen___closed__31_once, _init_l_Lean_Parser_Tactic_vcgen___closed__31);
v___x_410_ = ((lean_object*)(l_Lean_Parser_Tactic_invariantAlts___closed__3));
v___x_411_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_411_, 0, v___x_410_);
lean_ctor_set(v___x_411_, 1, v___x_409_);
return v___x_411_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_vcgen___closed__33(void){
_start:
{
lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_412_ = lean_obj_once(&l_Lean_Parser_Tactic_vcgen___closed__32, &l_Lean_Parser_Tactic_vcgen___closed__32_once, _init_l_Lean_Parser_Tactic_vcgen___closed__32);
v___x_413_ = ((lean_object*)(l_Lean_Parser_Tactic_vcgen___closed__27));
v___x_414_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_415_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_415_, 0, v___x_414_);
lean_ctor_set(v___x_415_, 1, v___x_413_);
lean_ctor_set(v___x_415_, 2, v___x_412_);
return v___x_415_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_vcgen___closed__34(void){
_start:
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_416_ = lean_obj_once(&l_Lean_Parser_Tactic_vcgen___closed__33, &l_Lean_Parser_Tactic_vcgen___closed__33_once, _init_l_Lean_Parser_Tactic_vcgen___closed__33);
v___x_417_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__9));
v___x_418_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_418_, 0, v___x_417_);
lean_ctor_set(v___x_418_, 1, v___x_416_);
return v___x_418_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_vcgen___closed__35(void){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_419_ = lean_obj_once(&l_Lean_Parser_Tactic_vcgen___closed__34, &l_Lean_Parser_Tactic_vcgen___closed__34_once, _init_l_Lean_Parser_Tactic_vcgen___closed__34);
v___x_420_ = lean_obj_once(&l_Lean_Parser_Tactic_vcgen___closed__25, &l_Lean_Parser_Tactic_vcgen___closed__25_once, _init_l_Lean_Parser_Tactic_vcgen___closed__25);
v___x_421_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_422_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_422_, 0, v___x_421_);
lean_ctor_set(v___x_422_, 1, v___x_420_);
lean_ctor_set(v___x_422_, 2, v___x_419_);
return v___x_422_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_vcgen___closed__36(void){
_start:
{
lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_423_ = l_Lean_Parser_Tactic_invariantAlts;
v___x_424_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__9));
v___x_425_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_425_, 0, v___x_424_);
lean_ctor_set(v___x_425_, 1, v___x_423_);
return v___x_425_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_vcgen___closed__37(void){
_start:
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_426_ = lean_obj_once(&l_Lean_Parser_Tactic_vcgen___closed__36, &l_Lean_Parser_Tactic_vcgen___closed__36_once, _init_l_Lean_Parser_Tactic_vcgen___closed__36);
v___x_427_ = lean_obj_once(&l_Lean_Parser_Tactic_vcgen___closed__35, &l_Lean_Parser_Tactic_vcgen___closed__35_once, _init_l_Lean_Parser_Tactic_vcgen___closed__35);
v___x_428_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_429_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_429_, 0, v___x_428_);
lean_ctor_set(v___x_429_, 1, v___x_427_);
lean_ctor_set(v___x_429_, 2, v___x_426_);
return v___x_429_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_vcgen___closed__51(void){
_start:
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_471_ = ((lean_object*)(l_Lean_Parser_Tactic_vcgen___closed__50));
v___x_472_ = lean_obj_once(&l_Lean_Parser_Tactic_vcgen___closed__37, &l_Lean_Parser_Tactic_vcgen___closed__37_once, _init_l_Lean_Parser_Tactic_vcgen___closed__37);
v___x_473_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_474_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_474_, 0, v___x_473_);
lean_ctor_set(v___x_474_, 1, v___x_472_);
lean_ctor_set(v___x_474_, 2, v___x_471_);
return v___x_474_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_vcgen___closed__56(void){
_start:
{
lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_486_ = ((lean_object*)(l_Lean_Parser_Tactic_vcgen___closed__55));
v___x_487_ = lean_obj_once(&l_Lean_Parser_Tactic_vcgen___closed__51, &l_Lean_Parser_Tactic_vcgen___closed__51_once, _init_l_Lean_Parser_Tactic_vcgen___closed__51);
v___x_488_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_489_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_489_, 0, v___x_488_);
lean_ctor_set(v___x_489_, 1, v___x_487_);
lean_ctor_set(v___x_489_, 2, v___x_486_);
return v___x_489_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_vcgen___closed__57(void){
_start:
{
lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_490_ = lean_obj_once(&l_Lean_Parser_Tactic_vcgen___closed__56, &l_Lean_Parser_Tactic_vcgen___closed__56_once, _init_l_Lean_Parser_Tactic_vcgen___closed__56);
v___x_491_ = lean_unsigned_to_nat(1022u);
v___x_492_ = ((lean_object*)(l_Lean_Parser_Tactic_vcgen___closed__1));
v___x_493_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_493_, 0, v___x_492_);
lean_ctor_set(v___x_493_, 1, v___x_491_);
lean_ctor_set(v___x_493_, 2, v___x_490_);
return v___x_493_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_vcgen(void){
_start:
{
lean_object* v___x_494_; 
v___x_494_ = lean_obj_once(&l_Lean_Parser_Tactic_vcgen___closed__57, &l_Lean_Parser_Tactic_vcgen___closed__57_once, _init_l_Lean_Parser_Tactic_vcgen___closed__57);
return v___x_494_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_vcgen___closed__2(void){
_start:
{
lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_502_ = lean_obj_once(&l_Lean_Parser_Tactic_vcgen___closed__51, &l_Lean_Parser_Tactic_vcgen___closed__51_once, _init_l_Lean_Parser_Tactic_vcgen___closed__51);
v___x_503_ = lean_unsigned_to_nat(1022u);
v___x_504_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_vcgen___closed__1));
v___x_505_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_505_, 0, v___x_504_);
lean_ctor_set(v___x_505_, 1, v___x_503_);
lean_ctor_set(v___x_505_, 2, v___x_502_);
return v___x_505_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_vcgen(void){
_start:
{
lean_object* v___x_506_; 
v___x_506_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_vcgen___closed__2, &l_Lean_Parser_Tactic_Grind_vcgen___closed__2_once, _init_l_Lean_Parser_Tactic_Grind_vcgen___closed__2);
return v___x_506_;
}
}
lean_object* runtime_initialize_Init_Grind_Interactive(uint8_t builtin);
lean_object* runtime_initialize_Init_NotationExtra(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_WP_Tactic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Grind_Interactive(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_NotationExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_WP_Tactic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Lean_Parser_Tactic_invariantDotAlt = _init_l_Lean_Parser_Tactic_invariantDotAlt();
lean_mark_persistent(l_Lean_Parser_Tactic_invariantDotAlt);
l_Lean_Parser_Tactic_invariantCaseAlt = _init_l_Lean_Parser_Tactic_invariantCaseAlt();
lean_mark_persistent(l_Lean_Parser_Tactic_invariantCaseAlt);
l_Lean_Parser_Tactic_invariantAlts = _init_l_Lean_Parser_Tactic_invariantAlts();
lean_mark_persistent(l_Lean_Parser_Tactic_invariantAlts);
l_Lean_Parser_Tactic_frameAlt = _init_l_Lean_Parser_Tactic_frameAlt();
lean_mark_persistent(l_Lean_Parser_Tactic_frameAlt);
l_Lean_Parser_Category_vcgenDischarge = _init_l_Lean_Parser_Category_vcgenDischarge();
lean_mark_persistent(l_Lean_Parser_Category_vcgenDischarge);
l_Lean_Parser_Tactic_vcgen = _init_l_Lean_Parser_Tactic_vcgen();
lean_mark_persistent(l_Lean_Parser_Tactic_vcgen);
l_Lean_Parser_Tactic_Grind_vcgen = _init_l_Lean_Parser_Tactic_Grind_vcgen();
lean_mark_persistent(l_Lean_Parser_Tactic_Grind_vcgen);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Grind_Interactive(uint8_t builtin);
lean_object* initialize_Init_NotationExtra(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_WP_Tactic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Interactive(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_NotationExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_WP_Tactic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_WP_Tactic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_WP_Tactic(builtin);
}
#ifdef __cplusplus
}
#endif

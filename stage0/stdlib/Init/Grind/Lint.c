// Lean compiler output
// Module: Init.Grind.Lint
// Imports: public import Init.Tactics
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
extern lean_object* l_Lean_Parser_Tactic_configItem;
static const lean_string_object l_Lean_Grind_grindLintCheck___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Grind_grindLintCheck___closed__0 = (const lean_object*)&l_Lean_Grind_grindLintCheck___closed__0_value;
static const lean_string_object l_Lean_Grind_grindLintCheck___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l_Lean_Grind_grindLintCheck___closed__1 = (const lean_object*)&l_Lean_Grind_grindLintCheck___closed__1_value;
static const lean_string_object l_Lean_Grind_grindLintCheck___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "grindLintCheck"};
static const lean_object* l_Lean_Grind_grindLintCheck___closed__2 = (const lean_object*)&l_Lean_Grind_grindLintCheck___closed__2_value;
static const lean_ctor_object l_Lean_Grind_grindLintCheck___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Grind_grindLintCheck___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Grind_grindLintCheck___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_grindLintCheck___closed__3_value_aux_0),((lean_object*)&l_Lean_Grind_grindLintCheck___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Grind_grindLintCheck___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_grindLintCheck___closed__3_value_aux_1),((lean_object*)&l_Lean_Grind_grindLintCheck___closed__2_value),LEAN_SCALAR_PTR_LITERAL(62, 113, 74, 13, 3, 158, 65, 234)}};
static const lean_object* l_Lean_Grind_grindLintCheck___closed__3 = (const lean_object*)&l_Lean_Grind_grindLintCheck___closed__3_value;
static const lean_string_object l_Lean_Grind_grindLintCheck___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Lean_Grind_grindLintCheck___closed__4 = (const lean_object*)&l_Lean_Grind_grindLintCheck___closed__4_value;
static const lean_ctor_object l_Lean_Grind_grindLintCheck___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Grind_grindLintCheck___closed__4_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Lean_Grind_grindLintCheck___closed__5 = (const lean_object*)&l_Lean_Grind_grindLintCheck___closed__5_value;
static const lean_string_object l_Lean_Grind_grindLintCheck___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "#grind_lint"};
static const lean_object* l_Lean_Grind_grindLintCheck___closed__6 = (const lean_object*)&l_Lean_Grind_grindLintCheck___closed__6_value;
static const lean_ctor_object l_Lean_Grind_grindLintCheck___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Grind_grindLintCheck___closed__6_value)}};
static const lean_object* l_Lean_Grind_grindLintCheck___closed__7 = (const lean_object*)&l_Lean_Grind_grindLintCheck___closed__7_value;
static const lean_string_object l_Lean_Grind_grindLintCheck___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "ppSpace"};
static const lean_object* l_Lean_Grind_grindLintCheck___closed__8 = (const lean_object*)&l_Lean_Grind_grindLintCheck___closed__8_value;
static const lean_ctor_object l_Lean_Grind_grindLintCheck___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Grind_grindLintCheck___closed__8_value),LEAN_SCALAR_PTR_LITERAL(207, 47, 58, 43, 30, 240, 125, 246)}};
static const lean_object* l_Lean_Grind_grindLintCheck___closed__9 = (const lean_object*)&l_Lean_Grind_grindLintCheck___closed__9_value;
static const lean_ctor_object l_Lean_Grind_grindLintCheck___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Grind_grindLintCheck___closed__9_value)}};
static const lean_object* l_Lean_Grind_grindLintCheck___closed__10 = (const lean_object*)&l_Lean_Grind_grindLintCheck___closed__10_value;
static const lean_ctor_object l_Lean_Grind_grindLintCheck___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Grind_grindLintCheck___closed__5_value),((lean_object*)&l_Lean_Grind_grindLintCheck___closed__7_value),((lean_object*)&l_Lean_Grind_grindLintCheck___closed__10_value)}};
static const lean_object* l_Lean_Grind_grindLintCheck___closed__11 = (const lean_object*)&l_Lean_Grind_grindLintCheck___closed__11_value;
static const lean_string_object l_Lean_Grind_grindLintCheck___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "check"};
static const lean_object* l_Lean_Grind_grindLintCheck___closed__12 = (const lean_object*)&l_Lean_Grind_grindLintCheck___closed__12_value;
static const lean_ctor_object l_Lean_Grind_grindLintCheck___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Grind_grindLintCheck___closed__12_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Grind_grindLintCheck___closed__13 = (const lean_object*)&l_Lean_Grind_grindLintCheck___closed__13_value;
static const lean_ctor_object l_Lean_Grind_grindLintCheck___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Grind_grindLintCheck___closed__5_value),((lean_object*)&l_Lean_Grind_grindLintCheck___closed__11_value),((lean_object*)&l_Lean_Grind_grindLintCheck___closed__13_value)}};
static const lean_object* l_Lean_Grind_grindLintCheck___closed__14 = (const lean_object*)&l_Lean_Grind_grindLintCheck___closed__14_value;
static const lean_string_object l_Lean_Grind_grindLintCheck___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "many"};
static const lean_object* l_Lean_Grind_grindLintCheck___closed__15 = (const lean_object*)&l_Lean_Grind_grindLintCheck___closed__15_value;
static const lean_ctor_object l_Lean_Grind_grindLintCheck___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Grind_grindLintCheck___closed__15_value),LEAN_SCALAR_PTR_LITERAL(41, 35, 40, 86, 189, 97, 244, 31)}};
static const lean_object* l_Lean_Grind_grindLintCheck___closed__16 = (const lean_object*)&l_Lean_Grind_grindLintCheck___closed__16_value;
static lean_once_cell_t l_Lean_Grind_grindLintCheck___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_grindLintCheck___closed__17;
static lean_once_cell_t l_Lean_Grind_grindLintCheck___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_grindLintCheck___closed__18;
static lean_once_cell_t l_Lean_Grind_grindLintCheck___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_grindLintCheck___closed__19;
static const lean_string_object l_Lean_Grind_grindLintCheck___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "optional"};
static const lean_object* l_Lean_Grind_grindLintCheck___closed__20 = (const lean_object*)&l_Lean_Grind_grindLintCheck___closed__20_value;
static const lean_ctor_object l_Lean_Grind_grindLintCheck___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Grind_grindLintCheck___closed__20_value),LEAN_SCALAR_PTR_LITERAL(233, 141, 154, 50, 143, 135, 42, 252)}};
static const lean_object* l_Lean_Grind_grindLintCheck___closed__21 = (const lean_object*)&l_Lean_Grind_grindLintCheck___closed__21_value;
static const lean_string_object l_Lean_Grind_grindLintCheck___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "in"};
static const lean_object* l_Lean_Grind_grindLintCheck___closed__22 = (const lean_object*)&l_Lean_Grind_grindLintCheck___closed__22_value;
static const lean_ctor_object l_Lean_Grind_grindLintCheck___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Grind_grindLintCheck___closed__22_value)}};
static const lean_object* l_Lean_Grind_grindLintCheck___closed__23 = (const lean_object*)&l_Lean_Grind_grindLintCheck___closed__23_value;
static const lean_ctor_object l_Lean_Grind_grindLintCheck___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Grind_grindLintCheck___closed__5_value),((lean_object*)&l_Lean_Grind_grindLintCheck___closed__10_value),((lean_object*)&l_Lean_Grind_grindLintCheck___closed__23_value)}};
static const lean_object* l_Lean_Grind_grindLintCheck___closed__24 = (const lean_object*)&l_Lean_Grind_grindLintCheck___closed__24_value;
static const lean_string_object l_Lean_Grind_grindLintCheck___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "module"};
static const lean_object* l_Lean_Grind_grindLintCheck___closed__25 = (const lean_object*)&l_Lean_Grind_grindLintCheck___closed__25_value;
static const lean_ctor_object l_Lean_Grind_grindLintCheck___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Grind_grindLintCheck___closed__25_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Grind_grindLintCheck___closed__26 = (const lean_object*)&l_Lean_Grind_grindLintCheck___closed__26_value;
static const lean_ctor_object l_Lean_Grind_grindLintCheck___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Grind_grindLintCheck___closed__5_value),((lean_object*)&l_Lean_Grind_grindLintCheck___closed__10_value),((lean_object*)&l_Lean_Grind_grindLintCheck___closed__26_value)}};
static const lean_object* l_Lean_Grind_grindLintCheck___closed__27 = (const lean_object*)&l_Lean_Grind_grindLintCheck___closed__27_value;
static const lean_ctor_object l_Lean_Grind_grindLintCheck___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_grindLintCheck___closed__21_value),((lean_object*)&l_Lean_Grind_grindLintCheck___closed__27_value)}};
static const lean_object* l_Lean_Grind_grindLintCheck___closed__28 = (const lean_object*)&l_Lean_Grind_grindLintCheck___closed__28_value;
static const lean_ctor_object l_Lean_Grind_grindLintCheck___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Grind_grindLintCheck___closed__5_value),((lean_object*)&l_Lean_Grind_grindLintCheck___closed__24_value),((lean_object*)&l_Lean_Grind_grindLintCheck___closed__28_value)}};
static const lean_object* l_Lean_Grind_grindLintCheck___closed__29 = (const lean_object*)&l_Lean_Grind_grindLintCheck___closed__29_value;
static const lean_string_object l_Lean_Grind_grindLintCheck___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "many1"};
static const lean_object* l_Lean_Grind_grindLintCheck___closed__30 = (const lean_object*)&l_Lean_Grind_grindLintCheck___closed__30_value;
static const lean_ctor_object l_Lean_Grind_grindLintCheck___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Grind_grindLintCheck___closed__30_value),LEAN_SCALAR_PTR_LITERAL(55, 136, 52, 6, 12, 19, 78, 239)}};
static const lean_object* l_Lean_Grind_grindLintCheck___closed__31 = (const lean_object*)&l_Lean_Grind_grindLintCheck___closed__31_value;
static const lean_string_object l_Lean_Grind_grindLintCheck___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Grind_grindLintCheck___closed__32 = (const lean_object*)&l_Lean_Grind_grindLintCheck___closed__32_value;
static const lean_ctor_object l_Lean_Grind_grindLintCheck___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Grind_grindLintCheck___closed__32_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Grind_grindLintCheck___closed__33 = (const lean_object*)&l_Lean_Grind_grindLintCheck___closed__33_value;
static const lean_ctor_object l_Lean_Grind_grindLintCheck___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Grind_grindLintCheck___closed__33_value)}};
static const lean_object* l_Lean_Grind_grindLintCheck___closed__34 = (const lean_object*)&l_Lean_Grind_grindLintCheck___closed__34_value;
static const lean_ctor_object l_Lean_Grind_grindLintCheck___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_grindLintCheck___closed__31_value),((lean_object*)&l_Lean_Grind_grindLintCheck___closed__34_value)}};
static const lean_object* l_Lean_Grind_grindLintCheck___closed__35 = (const lean_object*)&l_Lean_Grind_grindLintCheck___closed__35_value;
static const lean_ctor_object l_Lean_Grind_grindLintCheck___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Grind_grindLintCheck___closed__5_value),((lean_object*)&l_Lean_Grind_grindLintCheck___closed__29_value),((lean_object*)&l_Lean_Grind_grindLintCheck___closed__35_value)}};
static const lean_object* l_Lean_Grind_grindLintCheck___closed__36 = (const lean_object*)&l_Lean_Grind_grindLintCheck___closed__36_value;
static const lean_ctor_object l_Lean_Grind_grindLintCheck___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_grindLintCheck___closed__21_value),((lean_object*)&l_Lean_Grind_grindLintCheck___closed__36_value)}};
static const lean_object* l_Lean_Grind_grindLintCheck___closed__37 = (const lean_object*)&l_Lean_Grind_grindLintCheck___closed__37_value;
static lean_once_cell_t l_Lean_Grind_grindLintCheck___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_grindLintCheck___closed__38;
static lean_once_cell_t l_Lean_Grind_grindLintCheck___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_grindLintCheck___closed__39;
LEAN_EXPORT lean_object* l_Lean_Grind_grindLintCheck;
static const lean_string_object l_Lean_Grind_grindLintInspect___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "grindLintInspect"};
static const lean_object* l_Lean_Grind_grindLintInspect___closed__0 = (const lean_object*)&l_Lean_Grind_grindLintInspect___closed__0_value;
static const lean_ctor_object l_Lean_Grind_grindLintInspect___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Grind_grindLintCheck___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Grind_grindLintInspect___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_grindLintInspect___closed__1_value_aux_0),((lean_object*)&l_Lean_Grind_grindLintCheck___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Grind_grindLintInspect___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_grindLintInspect___closed__1_value_aux_1),((lean_object*)&l_Lean_Grind_grindLintInspect___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 56, 130, 46, 162, 240, 182, 8)}};
static const lean_object* l_Lean_Grind_grindLintInspect___closed__1 = (const lean_object*)&l_Lean_Grind_grindLintInspect___closed__1_value;
static const lean_string_object l_Lean_Grind_grindLintInspect___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "inspect"};
static const lean_object* l_Lean_Grind_grindLintInspect___closed__2 = (const lean_object*)&l_Lean_Grind_grindLintInspect___closed__2_value;
static const lean_ctor_object l_Lean_Grind_grindLintInspect___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Grind_grindLintInspect___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Grind_grindLintInspect___closed__3 = (const lean_object*)&l_Lean_Grind_grindLintInspect___closed__3_value;
static const lean_ctor_object l_Lean_Grind_grindLintInspect___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Grind_grindLintCheck___closed__5_value),((lean_object*)&l_Lean_Grind_grindLintCheck___closed__11_value),((lean_object*)&l_Lean_Grind_grindLintInspect___closed__3_value)}};
static const lean_object* l_Lean_Grind_grindLintInspect___closed__4 = (const lean_object*)&l_Lean_Grind_grindLintInspect___closed__4_value;
static lean_once_cell_t l_Lean_Grind_grindLintInspect___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_grindLintInspect___closed__5;
static lean_once_cell_t l_Lean_Grind_grindLintInspect___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_grindLintInspect___closed__6;
static lean_once_cell_t l_Lean_Grind_grindLintInspect___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_grindLintInspect___closed__7;
LEAN_EXPORT lean_object* l_Lean_Grind_grindLintInspect;
static const lean_string_object l_Lean_Grind_grindLintMute___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "grindLintMute"};
static const lean_object* l_Lean_Grind_grindLintMute___closed__0 = (const lean_object*)&l_Lean_Grind_grindLintMute___closed__0_value;
static const lean_ctor_object l_Lean_Grind_grindLintMute___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Grind_grindLintCheck___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Grind_grindLintMute___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_grindLintMute___closed__1_value_aux_0),((lean_object*)&l_Lean_Grind_grindLintCheck___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Grind_grindLintMute___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_grindLintMute___closed__1_value_aux_1),((lean_object*)&l_Lean_Grind_grindLintMute___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 30, 63, 16, 186, 128, 138, 7)}};
static const lean_object* l_Lean_Grind_grindLintMute___closed__1 = (const lean_object*)&l_Lean_Grind_grindLintMute___closed__1_value;
static const lean_string_object l_Lean_Grind_grindLintMute___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "mute"};
static const lean_object* l_Lean_Grind_grindLintMute___closed__2 = (const lean_object*)&l_Lean_Grind_grindLintMute___closed__2_value;
static const lean_ctor_object l_Lean_Grind_grindLintMute___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Grind_grindLintMute___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Grind_grindLintMute___closed__3 = (const lean_object*)&l_Lean_Grind_grindLintMute___closed__3_value;
static const lean_ctor_object l_Lean_Grind_grindLintMute___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Grind_grindLintCheck___closed__5_value),((lean_object*)&l_Lean_Grind_grindLintCheck___closed__11_value),((lean_object*)&l_Lean_Grind_grindLintMute___closed__3_value)}};
static const lean_object* l_Lean_Grind_grindLintMute___closed__4 = (const lean_object*)&l_Lean_Grind_grindLintMute___closed__4_value;
static const lean_ctor_object l_Lean_Grind_grindLintMute___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Grind_grindLintCheck___closed__5_value),((lean_object*)&l_Lean_Grind_grindLintMute___closed__4_value),((lean_object*)&l_Lean_Grind_grindLintCheck___closed__35_value)}};
static const lean_object* l_Lean_Grind_grindLintMute___closed__5 = (const lean_object*)&l_Lean_Grind_grindLintMute___closed__5_value;
static const lean_ctor_object l_Lean_Grind_grindLintMute___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Grind_grindLintMute___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Grind_grindLintMute___closed__5_value)}};
static const lean_object* l_Lean_Grind_grindLintMute___closed__6 = (const lean_object*)&l_Lean_Grind_grindLintMute___closed__6_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_grindLintMute = (const lean_object*)&l_Lean_Grind_grindLintMute___closed__6_value;
static const lean_string_object l_Lean_Grind_grindLintSkip___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "grindLintSkip"};
static const lean_object* l_Lean_Grind_grindLintSkip___closed__0 = (const lean_object*)&l_Lean_Grind_grindLintSkip___closed__0_value;
static const lean_ctor_object l_Lean_Grind_grindLintSkip___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Grind_grindLintCheck___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Grind_grindLintSkip___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_grindLintSkip___closed__1_value_aux_0),((lean_object*)&l_Lean_Grind_grindLintCheck___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Grind_grindLintSkip___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_grindLintSkip___closed__1_value_aux_1),((lean_object*)&l_Lean_Grind_grindLintSkip___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 168, 241, 99, 13, 160, 45, 13)}};
static const lean_object* l_Lean_Grind_grindLintSkip___closed__1 = (const lean_object*)&l_Lean_Grind_grindLintSkip___closed__1_value;
static const lean_string_object l_Lean_Grind_grindLintSkip___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "skip"};
static const lean_object* l_Lean_Grind_grindLintSkip___closed__2 = (const lean_object*)&l_Lean_Grind_grindLintSkip___closed__2_value;
static const lean_ctor_object l_Lean_Grind_grindLintSkip___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Grind_grindLintSkip___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Grind_grindLintSkip___closed__3 = (const lean_object*)&l_Lean_Grind_grindLintSkip___closed__3_value;
static const lean_ctor_object l_Lean_Grind_grindLintSkip___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Grind_grindLintCheck___closed__5_value),((lean_object*)&l_Lean_Grind_grindLintCheck___closed__11_value),((lean_object*)&l_Lean_Grind_grindLintSkip___closed__3_value)}};
static const lean_object* l_Lean_Grind_grindLintSkip___closed__4 = (const lean_object*)&l_Lean_Grind_grindLintSkip___closed__4_value;
static const lean_string_object l_Lean_Grind_grindLintSkip___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "suffix"};
static const lean_object* l_Lean_Grind_grindLintSkip___closed__5 = (const lean_object*)&l_Lean_Grind_grindLintSkip___closed__5_value;
static const lean_ctor_object l_Lean_Grind_grindLintSkip___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Grind_grindLintSkip___closed__5_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Grind_grindLintSkip___closed__6 = (const lean_object*)&l_Lean_Grind_grindLintSkip___closed__6_value;
static const lean_ctor_object l_Lean_Grind_grindLintSkip___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Grind_grindLintCheck___closed__5_value),((lean_object*)&l_Lean_Grind_grindLintCheck___closed__10_value),((lean_object*)&l_Lean_Grind_grindLintSkip___closed__6_value)}};
static const lean_object* l_Lean_Grind_grindLintSkip___closed__7 = (const lean_object*)&l_Lean_Grind_grindLintSkip___closed__7_value;
static const lean_ctor_object l_Lean_Grind_grindLintSkip___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_grindLintCheck___closed__21_value),((lean_object*)&l_Lean_Grind_grindLintSkip___closed__7_value)}};
static const lean_object* l_Lean_Grind_grindLintSkip___closed__8 = (const lean_object*)&l_Lean_Grind_grindLintSkip___closed__8_value;
static const lean_ctor_object l_Lean_Grind_grindLintSkip___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Grind_grindLintCheck___closed__5_value),((lean_object*)&l_Lean_Grind_grindLintSkip___closed__4_value),((lean_object*)&l_Lean_Grind_grindLintSkip___closed__8_value)}};
static const lean_object* l_Lean_Grind_grindLintSkip___closed__9 = (const lean_object*)&l_Lean_Grind_grindLintSkip___closed__9_value;
static const lean_ctor_object l_Lean_Grind_grindLintSkip___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Grind_grindLintCheck___closed__5_value),((lean_object*)&l_Lean_Grind_grindLintSkip___closed__9_value),((lean_object*)&l_Lean_Grind_grindLintCheck___closed__35_value)}};
static const lean_object* l_Lean_Grind_grindLintSkip___closed__10 = (const lean_object*)&l_Lean_Grind_grindLintSkip___closed__10_value;
static const lean_ctor_object l_Lean_Grind_grindLintSkip___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Grind_grindLintSkip___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Grind_grindLintSkip___closed__10_value)}};
static const lean_object* l_Lean_Grind_grindLintSkip___closed__11 = (const lean_object*)&l_Lean_Grind_grindLintSkip___closed__11_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_grindLintSkip = (const lean_object*)&l_Lean_Grind_grindLintSkip___closed__11_value;
static lean_object* _init_l_Lean_Grind_grindLintCheck___closed__17(void){
_start:
{
lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_34_ = l_Lean_Parser_Tactic_configItem;
v___x_35_ = ((lean_object*)(l_Lean_Grind_grindLintCheck___closed__10));
v___x_36_ = ((lean_object*)(l_Lean_Grind_grindLintCheck___closed__5));
v___x_37_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_37_, 0, v___x_36_);
lean_ctor_set(v___x_37_, 1, v___x_35_);
lean_ctor_set(v___x_37_, 2, v___x_34_);
return v___x_37_;
}
}
static lean_object* _init_l_Lean_Grind_grindLintCheck___closed__18(void){
_start:
{
lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_38_ = lean_obj_once(&l_Lean_Grind_grindLintCheck___closed__17, &l_Lean_Grind_grindLintCheck___closed__17_once, _init_l_Lean_Grind_grindLintCheck___closed__17);
v___x_39_ = ((lean_object*)(l_Lean_Grind_grindLintCheck___closed__16));
v___x_40_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_40_, 0, v___x_39_);
lean_ctor_set(v___x_40_, 1, v___x_38_);
return v___x_40_;
}
}
static lean_object* _init_l_Lean_Grind_grindLintCheck___closed__19(void){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_41_ = lean_obj_once(&l_Lean_Grind_grindLintCheck___closed__18, &l_Lean_Grind_grindLintCheck___closed__18_once, _init_l_Lean_Grind_grindLintCheck___closed__18);
v___x_42_ = ((lean_object*)(l_Lean_Grind_grindLintCheck___closed__14));
v___x_43_ = ((lean_object*)(l_Lean_Grind_grindLintCheck___closed__5));
v___x_44_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_44_, 0, v___x_43_);
lean_ctor_set(v___x_44_, 1, v___x_42_);
lean_ctor_set(v___x_44_, 2, v___x_41_);
return v___x_44_;
}
}
static lean_object* _init_l_Lean_Grind_grindLintCheck___closed__38(void){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_88_ = ((lean_object*)(l_Lean_Grind_grindLintCheck___closed__37));
v___x_89_ = lean_obj_once(&l_Lean_Grind_grindLintCheck___closed__19, &l_Lean_Grind_grindLintCheck___closed__19_once, _init_l_Lean_Grind_grindLintCheck___closed__19);
v___x_90_ = ((lean_object*)(l_Lean_Grind_grindLintCheck___closed__5));
v___x_91_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_91_, 0, v___x_90_);
lean_ctor_set(v___x_91_, 1, v___x_89_);
lean_ctor_set(v___x_91_, 2, v___x_88_);
return v___x_91_;
}
}
static lean_object* _init_l_Lean_Grind_grindLintCheck___closed__39(void){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_92_ = lean_obj_once(&l_Lean_Grind_grindLintCheck___closed__38, &l_Lean_Grind_grindLintCheck___closed__38_once, _init_l_Lean_Grind_grindLintCheck___closed__38);
v___x_93_ = lean_unsigned_to_nat(1022u);
v___x_94_ = ((lean_object*)(l_Lean_Grind_grindLintCheck___closed__3));
v___x_95_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_95_, 0, v___x_94_);
lean_ctor_set(v___x_95_, 1, v___x_93_);
lean_ctor_set(v___x_95_, 2, v___x_92_);
return v___x_95_;
}
}
static lean_object* _init_l_Lean_Grind_grindLintCheck(void){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = lean_obj_once(&l_Lean_Grind_grindLintCheck___closed__39, &l_Lean_Grind_grindLintCheck___closed__39_once, _init_l_Lean_Grind_grindLintCheck___closed__39);
return v___x_96_;
}
}
static lean_object* _init_l_Lean_Grind_grindLintInspect___closed__5(void){
_start:
{
lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_110_ = lean_obj_once(&l_Lean_Grind_grindLintCheck___closed__18, &l_Lean_Grind_grindLintCheck___closed__18_once, _init_l_Lean_Grind_grindLintCheck___closed__18);
v___x_111_ = ((lean_object*)(l_Lean_Grind_grindLintInspect___closed__4));
v___x_112_ = ((lean_object*)(l_Lean_Grind_grindLintCheck___closed__5));
v___x_113_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_113_, 0, v___x_112_);
lean_ctor_set(v___x_113_, 1, v___x_111_);
lean_ctor_set(v___x_113_, 2, v___x_110_);
return v___x_113_;
}
}
static lean_object* _init_l_Lean_Grind_grindLintInspect___closed__6(void){
_start:
{
lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_114_ = ((lean_object*)(l_Lean_Grind_grindLintCheck___closed__35));
v___x_115_ = lean_obj_once(&l_Lean_Grind_grindLintInspect___closed__5, &l_Lean_Grind_grindLintInspect___closed__5_once, _init_l_Lean_Grind_grindLintInspect___closed__5);
v___x_116_ = ((lean_object*)(l_Lean_Grind_grindLintCheck___closed__5));
v___x_117_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_117_, 0, v___x_116_);
lean_ctor_set(v___x_117_, 1, v___x_115_);
lean_ctor_set(v___x_117_, 2, v___x_114_);
return v___x_117_;
}
}
static lean_object* _init_l_Lean_Grind_grindLintInspect___closed__7(void){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_118_ = lean_obj_once(&l_Lean_Grind_grindLintInspect___closed__6, &l_Lean_Grind_grindLintInspect___closed__6_once, _init_l_Lean_Grind_grindLintInspect___closed__6);
v___x_119_ = lean_unsigned_to_nat(1022u);
v___x_120_ = ((lean_object*)(l_Lean_Grind_grindLintInspect___closed__1));
v___x_121_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_121_, 0, v___x_120_);
lean_ctor_set(v___x_121_, 1, v___x_119_);
lean_ctor_set(v___x_121_, 2, v___x_118_);
return v___x_121_;
}
}
static lean_object* _init_l_Lean_Grind_grindLintInspect(void){
_start:
{
lean_object* v___x_122_; 
v___x_122_ = lean_obj_once(&l_Lean_Grind_grindLintInspect___closed__7, &l_Lean_Grind_grindLintInspect___closed__7_once, _init_l_Lean_Grind_grindLintInspect___closed__7);
return v___x_122_;
}
}
lean_object* runtime_initialize_Init_Tactics(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Grind_Lint(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Grind_Lint(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Lean_Grind_grindLintCheck = _init_l_Lean_Grind_grindLintCheck();
lean_mark_persistent(l_Lean_Grind_grindLintCheck);
l_Lean_Grind_grindLintInspect = _init_l_Lean_Grind_grindLintInspect();
lean_mark_persistent(l_Lean_Grind_grindLintInspect);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Tactics(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Grind_Lint(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Lint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Grind_Lint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Grind_Lint(builtin);
}
#ifdef __cplusplus
}
#endif

// Lean compiler output
// Module: Init.Grind.Tactics
// Imports: public import Init.Core public import Init.Grind.Interactive
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
extern lean_object* l_Lean_Parser_Tactic_Grind_grindSeq;
extern lean_object* l_Lean_Parser_Tactic_grindParam;
lean_object* l_Lean_Name_mkStr1(lean_object*);
extern lean_object* l_Lean_Parser_Tactic_optConfig;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_grind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Parser_Tactic_grind___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_grind___closed__0_value;
static const lean_string_object l_Lean_Parser_Tactic_grind___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Parser_Tactic_grind___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_grind___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_grind___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Parser_Tactic_grind___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_grind___closed__2_value;
static const lean_string_object l_Lean_Parser_Tactic_grind___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l_Lean_Parser_Tactic_grind___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_grind___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_grind___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_grind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_grind___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_grind___closed__4_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_grind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_grind___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_grind___closed__4_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_grind___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_grind___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_grind___closed__4_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_grind___closed__3_value),LEAN_SCALAR_PTR_LITERAL(150, 98, 0, 78, 28, 79, 28, 100)}};
static const lean_object* l_Lean_Parser_Tactic_grind___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_grind___closed__4_value;
static const lean_string_object l_Lean_Parser_Tactic_grind___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Lean_Parser_Tactic_grind___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_grind___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_grind___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_grind___closed__5_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Lean_Parser_Tactic_grind___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_grind___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_grind___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_grind___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_grind___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_grind___closed__7_value;
static lean_once_cell_t l_Lean_Parser_Tactic_grind___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_grind___closed__8;
static const lean_string_object l_Lean_Parser_Tactic_grind___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "optional"};
static const lean_object* l_Lean_Parser_Tactic_grind___closed__9 = (const lean_object*)&l_Lean_Parser_Tactic_grind___closed__9_value;
static const lean_ctor_object l_Lean_Parser_Tactic_grind___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_grind___closed__9_value),LEAN_SCALAR_PTR_LITERAL(233, 141, 154, 50, 143, 135, 42, 252)}};
static const lean_object* l_Lean_Parser_Tactic_grind___closed__10 = (const lean_object*)&l_Lean_Parser_Tactic_grind___closed__10_value;
static const lean_string_object l_Lean_Parser_Tactic_grind___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " only"};
static const lean_object* l_Lean_Parser_Tactic_grind___closed__11 = (const lean_object*)&l_Lean_Parser_Tactic_grind___closed__11_value;
static const lean_ctor_object l_Lean_Parser_Tactic_grind___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_grind___closed__11_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_grind___closed__12 = (const lean_object*)&l_Lean_Parser_Tactic_grind___closed__12_value;
static const lean_ctor_object l_Lean_Parser_Tactic_grind___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_grind___closed__10_value),((lean_object*)&l_Lean_Parser_Tactic_grind___closed__12_value)}};
static const lean_object* l_Lean_Parser_Tactic_grind___closed__13 = (const lean_object*)&l_Lean_Parser_Tactic_grind___closed__13_value;
static lean_once_cell_t l_Lean_Parser_Tactic_grind___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_grind___closed__14;
static const lean_string_object l_Lean_Parser_Tactic_grind___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " ["};
static const lean_object* l_Lean_Parser_Tactic_grind___closed__15 = (const lean_object*)&l_Lean_Parser_Tactic_grind___closed__15_value;
static const lean_ctor_object l_Lean_Parser_Tactic_grind___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_grind___closed__15_value)}};
static const lean_object* l_Lean_Parser_Tactic_grind___closed__16 = (const lean_object*)&l_Lean_Parser_Tactic_grind___closed__16_value;
static const lean_string_object l_Lean_Parser_Tactic_grind___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "withoutPosition"};
static const lean_object* l_Lean_Parser_Tactic_grind___closed__17 = (const lean_object*)&l_Lean_Parser_Tactic_grind___closed__17_value;
static const lean_ctor_object l_Lean_Parser_Tactic_grind___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_grind___closed__17_value),LEAN_SCALAR_PTR_LITERAL(69, 6, 27, 142, 141, 165, 41, 16)}};
static const lean_object* l_Lean_Parser_Tactic_grind___closed__18 = (const lean_object*)&l_Lean_Parser_Tactic_grind___closed__18_value;
static const lean_string_object l_Lean_Parser_Tactic_grind___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_Parser_Tactic_grind___closed__19 = (const lean_object*)&l_Lean_Parser_Tactic_grind___closed__19_value;
static const lean_string_object l_Lean_Parser_Tactic_grind___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_Lean_Parser_Tactic_grind___closed__20 = (const lean_object*)&l_Lean_Parser_Tactic_grind___closed__20_value;
static const lean_ctor_object l_Lean_Parser_Tactic_grind___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_grind___closed__20_value)}};
static const lean_object* l_Lean_Parser_Tactic_grind___closed__21 = (const lean_object*)&l_Lean_Parser_Tactic_grind___closed__21_value;
static lean_once_cell_t l_Lean_Parser_Tactic_grind___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_grind___closed__22;
static lean_once_cell_t l_Lean_Parser_Tactic_grind___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_grind___closed__23;
static lean_once_cell_t l_Lean_Parser_Tactic_grind___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_grind___closed__24;
static const lean_string_object l_Lean_Parser_Tactic_grind___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_Parser_Tactic_grind___closed__25 = (const lean_object*)&l_Lean_Parser_Tactic_grind___closed__25_value;
static const lean_ctor_object l_Lean_Parser_Tactic_grind___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_grind___closed__25_value)}};
static const lean_object* l_Lean_Parser_Tactic_grind___closed__26 = (const lean_object*)&l_Lean_Parser_Tactic_grind___closed__26_value;
static lean_once_cell_t l_Lean_Parser_Tactic_grind___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_grind___closed__27;
static lean_once_cell_t l_Lean_Parser_Tactic_grind___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_grind___closed__28;
static lean_once_cell_t l_Lean_Parser_Tactic_grind___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_grind___closed__29;
static const lean_string_object l_Lean_Parser_Tactic_grind___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " => "};
static const lean_object* l_Lean_Parser_Tactic_grind___closed__30 = (const lean_object*)&l_Lean_Parser_Tactic_grind___closed__30_value;
static const lean_ctor_object l_Lean_Parser_Tactic_grind___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_grind___closed__30_value)}};
static const lean_object* l_Lean_Parser_Tactic_grind___closed__31 = (const lean_object*)&l_Lean_Parser_Tactic_grind___closed__31_value;
static lean_once_cell_t l_Lean_Parser_Tactic_grind___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_grind___closed__32;
static lean_once_cell_t l_Lean_Parser_Tactic_grind___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_grind___closed__33;
static lean_once_cell_t l_Lean_Parser_Tactic_grind___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_grind___closed__34;
static lean_once_cell_t l_Lean_Parser_Tactic_grind___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_grind___closed__35;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_grind;
static const lean_string_object l_Lean_Parser_Tactic_grindTrace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grindTrace"};
static const lean_object* l_Lean_Parser_Tactic_grindTrace___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_grindTrace___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_grindTrace___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_grind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_grindTrace___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_grindTrace___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_grind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_grindTrace___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_grindTrace___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_grind___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_grindTrace___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_grindTrace___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_grindTrace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(208, 245, 239, 189, 189, 113, 196, 115)}};
static const lean_object* l_Lean_Parser_Tactic_grindTrace___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_grindTrace___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_grindTrace___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "grind\?"};
static const lean_object* l_Lean_Parser_Tactic_grindTrace___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_grindTrace___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_grindTrace___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_grindTrace___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_grindTrace___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_grindTrace___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Tactic_grindTrace___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_grindTrace___closed__4;
static lean_once_cell_t l_Lean_Parser_Tactic_grindTrace___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_grindTrace___closed__5;
static lean_once_cell_t l_Lean_Parser_Tactic_grindTrace___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_grindTrace___closed__6;
static lean_once_cell_t l_Lean_Parser_Tactic_grindTrace___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_grindTrace___closed__7;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_grindTrace;
static const lean_string_object l_Lean_Parser_Tactic_sym___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "sym"};
static const lean_object* l_Lean_Parser_Tactic_sym___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_sym___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_sym___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_grind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_sym___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_sym___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_grind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_sym___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_sym___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_grind___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_sym___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_sym___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_sym___closed__0_value),LEAN_SCALAR_PTR_LITERAL(207, 55, 232, 82, 57, 183, 116, 37)}};
static const lean_object* l_Lean_Parser_Tactic_sym___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_sym___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_sym___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_sym___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_sym___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_sym___closed__2_value;
static lean_once_cell_t l_Lean_Parser_Tactic_sym___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_sym___closed__3;
static lean_once_cell_t l_Lean_Parser_Tactic_sym___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_sym___closed__4;
static lean_once_cell_t l_Lean_Parser_Tactic_sym___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_sym___closed__5;
static lean_once_cell_t l_Lean_Parser_Tactic_sym___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_sym___closed__6;
static lean_once_cell_t l_Lean_Parser_Tactic_sym___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_sym___closed__7;
static lean_once_cell_t l_Lean_Parser_Tactic_sym___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_sym___closed__8;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_sym;
static const lean_string_object l_Lean_Parser_Tactic_cutsat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "cutsat"};
static const lean_object* l_Lean_Parser_Tactic_cutsat___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_cutsat___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_cutsat___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_grind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_cutsat___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_cutsat___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_grind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_cutsat___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_cutsat___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_grind___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_cutsat___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_cutsat___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_cutsat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 143, 41, 132, 162, 171, 243, 34)}};
static const lean_object* l_Lean_Parser_Tactic_cutsat___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_cutsat___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_cutsat___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_cutsat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_cutsat___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_cutsat___closed__2_value;
static lean_once_cell_t l_Lean_Parser_Tactic_cutsat___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_cutsat___closed__3;
static lean_once_cell_t l_Lean_Parser_Tactic_cutsat___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_cutsat___closed__4;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_cutsat;
static const lean_string_object l_Lean_Parser_Tactic_lia___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "lia"};
static const lean_object* l_Lean_Parser_Tactic_lia___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_lia___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_lia___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_grind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_lia___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_lia___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_grind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_lia___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_lia___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_grind___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_lia___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_lia___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_lia___closed__0_value),LEAN_SCALAR_PTR_LITERAL(85, 74, 44, 139, 89, 35, 186, 8)}};
static const lean_object* l_Lean_Parser_Tactic_lia___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_lia___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_lia___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_lia___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_lia___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_lia___closed__2_value;
static lean_once_cell_t l_Lean_Parser_Tactic_lia___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_lia___closed__3;
static lean_once_cell_t l_Lean_Parser_Tactic_lia___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_lia___closed__4;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_lia;
static const lean_string_object l_Lean_Parser_Tactic_grind__order___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "grind_order"};
static const lean_object* l_Lean_Parser_Tactic_grind__order___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_grind__order___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_grind__order___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_grind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_grind__order___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_grind__order___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_grind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_grind__order___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_grind__order___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_grind___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_grind__order___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_grind__order___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_grind__order___closed__0_value),LEAN_SCALAR_PTR_LITERAL(47, 44, 144, 70, 207, 54, 125, 88)}};
static const lean_object* l_Lean_Parser_Tactic_grind__order___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_grind__order___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_grind__order___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_grind__order___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_grind__order___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_grind__order___closed__2_value;
static lean_once_cell_t l_Lean_Parser_Tactic_grind__order___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_grind__order___closed__3;
static lean_once_cell_t l_Lean_Parser_Tactic_grind__order___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_grind__order___closed__4;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_grind__order;
static const lean_string_object l_Lean_Parser_Tactic_grind__linarith___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "grind_linarith"};
static const lean_object* l_Lean_Parser_Tactic_grind__linarith___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_grind__linarith___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_grind__linarith___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_grind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_grind__linarith___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_grind__linarith___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_grind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_grind__linarith___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_grind__linarith___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_grind___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_grind__linarith___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_grind__linarith___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_grind__linarith___closed__0_value),LEAN_SCALAR_PTR_LITERAL(63, 70, 60, 37, 53, 143, 147, 85)}};
static const lean_object* l_Lean_Parser_Tactic_grind__linarith___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_grind__linarith___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_grind__linarith___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_grind__linarith___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_grind__linarith___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_grind__linarith___closed__2_value;
static lean_once_cell_t l_Lean_Parser_Tactic_grind__linarith___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_grind__linarith___closed__3;
static lean_once_cell_t l_Lean_Parser_Tactic_grind__linarith___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_grind__linarith___closed__4;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_grind__linarith;
static const lean_string_object l_Lean_Parser_Tactic_grobner___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "grobner"};
static const lean_object* l_Lean_Parser_Tactic_grobner___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_grobner___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_grobner___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_grind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_grobner___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_grobner___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_grind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_grobner___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_grobner___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_grind___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_grobner___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_grobner___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_grobner___closed__0_value),LEAN_SCALAR_PTR_LITERAL(241, 188, 100, 211, 106, 33, 144, 166)}};
static const lean_object* l_Lean_Parser_Tactic_grobner___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_grobner___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_grobner___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_grobner___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_grobner___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_grobner___closed__2_value;
static lean_once_cell_t l_Lean_Parser_Tactic_grobner___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_grobner___closed__3;
static lean_once_cell_t l_Lean_Parser_Tactic_grobner___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_grobner___closed__4;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_grobner;
static lean_object* _init_l_Lean_Parser_Tactic_grind___closed__8(void){
_start:
{
lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_16_ = l_Lean_Parser_Tactic_optConfig;
v___x_17_ = ((lean_object*)(l_Lean_Parser_Tactic_grind___closed__7));
v___x_18_ = ((lean_object*)(l_Lean_Parser_Tactic_grind___closed__6));
v___x_19_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_19_, 0, v___x_18_);
lean_ctor_set(v___x_19_, 1, v___x_17_);
lean_ctor_set(v___x_19_, 2, v___x_16_);
return v___x_19_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grind___closed__14(void){
_start:
{
lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_30_ = ((lean_object*)(l_Lean_Parser_Tactic_grind___closed__13));
v___x_31_ = lean_obj_once(&l_Lean_Parser_Tactic_grind___closed__8, &l_Lean_Parser_Tactic_grind___closed__8_once, _init_l_Lean_Parser_Tactic_grind___closed__8);
v___x_32_ = ((lean_object*)(l_Lean_Parser_Tactic_grind___closed__6));
v___x_33_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_33_, 0, v___x_32_);
lean_ctor_set(v___x_33_, 1, v___x_31_);
lean_ctor_set(v___x_33_, 2, v___x_30_);
return v___x_33_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grind___closed__22(void){
_start:
{
uint8_t v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_44_ = 0;
v___x_45_ = ((lean_object*)(l_Lean_Parser_Tactic_grind___closed__21));
v___x_46_ = ((lean_object*)(l_Lean_Parser_Tactic_grind___closed__19));
v___x_47_ = l_Lean_Parser_Tactic_grindParam;
v___x_48_ = lean_alloc_ctor(10, 3, 1);
lean_ctor_set(v___x_48_, 0, v___x_47_);
lean_ctor_set(v___x_48_, 1, v___x_46_);
lean_ctor_set(v___x_48_, 2, v___x_45_);
lean_ctor_set_uint8(v___x_48_, sizeof(void*)*3, v___x_44_);
return v___x_48_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grind___closed__23(void){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_49_ = lean_obj_once(&l_Lean_Parser_Tactic_grind___closed__22, &l_Lean_Parser_Tactic_grind___closed__22_once, _init_l_Lean_Parser_Tactic_grind___closed__22);
v___x_50_ = ((lean_object*)(l_Lean_Parser_Tactic_grind___closed__18));
v___x_51_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_51_, 0, v___x_50_);
lean_ctor_set(v___x_51_, 1, v___x_49_);
return v___x_51_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grind___closed__24(void){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_52_ = lean_obj_once(&l_Lean_Parser_Tactic_grind___closed__23, &l_Lean_Parser_Tactic_grind___closed__23_once, _init_l_Lean_Parser_Tactic_grind___closed__23);
v___x_53_ = ((lean_object*)(l_Lean_Parser_Tactic_grind___closed__16));
v___x_54_ = ((lean_object*)(l_Lean_Parser_Tactic_grind___closed__6));
v___x_55_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_55_, 0, v___x_54_);
lean_ctor_set(v___x_55_, 1, v___x_53_);
lean_ctor_set(v___x_55_, 2, v___x_52_);
return v___x_55_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grind___closed__27(void){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_59_ = ((lean_object*)(l_Lean_Parser_Tactic_grind___closed__26));
v___x_60_ = lean_obj_once(&l_Lean_Parser_Tactic_grind___closed__24, &l_Lean_Parser_Tactic_grind___closed__24_once, _init_l_Lean_Parser_Tactic_grind___closed__24);
v___x_61_ = ((lean_object*)(l_Lean_Parser_Tactic_grind___closed__6));
v___x_62_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_62_, 0, v___x_61_);
lean_ctor_set(v___x_62_, 1, v___x_60_);
lean_ctor_set(v___x_62_, 2, v___x_59_);
return v___x_62_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grind___closed__28(void){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_63_ = lean_obj_once(&l_Lean_Parser_Tactic_grind___closed__27, &l_Lean_Parser_Tactic_grind___closed__27_once, _init_l_Lean_Parser_Tactic_grind___closed__27);
v___x_64_ = ((lean_object*)(l_Lean_Parser_Tactic_grind___closed__10));
v___x_65_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_65_, 0, v___x_64_);
lean_ctor_set(v___x_65_, 1, v___x_63_);
return v___x_65_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grind___closed__29(void){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_66_ = lean_obj_once(&l_Lean_Parser_Tactic_grind___closed__28, &l_Lean_Parser_Tactic_grind___closed__28_once, _init_l_Lean_Parser_Tactic_grind___closed__28);
v___x_67_ = lean_obj_once(&l_Lean_Parser_Tactic_grind___closed__14, &l_Lean_Parser_Tactic_grind___closed__14_once, _init_l_Lean_Parser_Tactic_grind___closed__14);
v___x_68_ = ((lean_object*)(l_Lean_Parser_Tactic_grind___closed__6));
v___x_69_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_69_, 0, v___x_68_);
lean_ctor_set(v___x_69_, 1, v___x_67_);
lean_ctor_set(v___x_69_, 2, v___x_66_);
return v___x_69_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grind___closed__32(void){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_73_ = l_Lean_Parser_Tactic_Grind_grindSeq;
v___x_74_ = ((lean_object*)(l_Lean_Parser_Tactic_grind___closed__31));
v___x_75_ = ((lean_object*)(l_Lean_Parser_Tactic_grind___closed__6));
v___x_76_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_76_, 0, v___x_75_);
lean_ctor_set(v___x_76_, 1, v___x_74_);
lean_ctor_set(v___x_76_, 2, v___x_73_);
return v___x_76_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grind___closed__33(void){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_77_ = lean_obj_once(&l_Lean_Parser_Tactic_grind___closed__32, &l_Lean_Parser_Tactic_grind___closed__32_once, _init_l_Lean_Parser_Tactic_grind___closed__32);
v___x_78_ = ((lean_object*)(l_Lean_Parser_Tactic_grind___closed__10));
v___x_79_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_79_, 0, v___x_78_);
lean_ctor_set(v___x_79_, 1, v___x_77_);
return v___x_79_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grind___closed__34(void){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_80_ = lean_obj_once(&l_Lean_Parser_Tactic_grind___closed__33, &l_Lean_Parser_Tactic_grind___closed__33_once, _init_l_Lean_Parser_Tactic_grind___closed__33);
v___x_81_ = lean_obj_once(&l_Lean_Parser_Tactic_grind___closed__29, &l_Lean_Parser_Tactic_grind___closed__29_once, _init_l_Lean_Parser_Tactic_grind___closed__29);
v___x_82_ = ((lean_object*)(l_Lean_Parser_Tactic_grind___closed__6));
v___x_83_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_83_, 0, v___x_82_);
lean_ctor_set(v___x_83_, 1, v___x_81_);
lean_ctor_set(v___x_83_, 2, v___x_80_);
return v___x_83_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grind___closed__35(void){
_start:
{
lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_84_ = lean_obj_once(&l_Lean_Parser_Tactic_grind___closed__34, &l_Lean_Parser_Tactic_grind___closed__34_once, _init_l_Lean_Parser_Tactic_grind___closed__34);
v___x_85_ = lean_unsigned_to_nat(1022u);
v___x_86_ = ((lean_object*)(l_Lean_Parser_Tactic_grind___closed__4));
v___x_87_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_87_, 0, v___x_86_);
lean_ctor_set(v___x_87_, 1, v___x_85_);
lean_ctor_set(v___x_87_, 2, v___x_84_);
return v___x_87_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grind(void){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = lean_obj_once(&l_Lean_Parser_Tactic_grind___closed__35, &l_Lean_Parser_Tactic_grind___closed__35_once, _init_l_Lean_Parser_Tactic_grind___closed__35);
return v___x_88_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grindTrace___closed__4(void){
_start:
{
lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_99_ = l_Lean_Parser_Tactic_optConfig;
v___x_100_ = ((lean_object*)(l_Lean_Parser_Tactic_grindTrace___closed__3));
v___x_101_ = ((lean_object*)(l_Lean_Parser_Tactic_grind___closed__6));
v___x_102_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_102_, 0, v___x_101_);
lean_ctor_set(v___x_102_, 1, v___x_100_);
lean_ctor_set(v___x_102_, 2, v___x_99_);
return v___x_102_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grindTrace___closed__5(void){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_103_ = ((lean_object*)(l_Lean_Parser_Tactic_grind___closed__13));
v___x_104_ = lean_obj_once(&l_Lean_Parser_Tactic_grindTrace___closed__4, &l_Lean_Parser_Tactic_grindTrace___closed__4_once, _init_l_Lean_Parser_Tactic_grindTrace___closed__4);
v___x_105_ = ((lean_object*)(l_Lean_Parser_Tactic_grind___closed__6));
v___x_106_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_106_, 0, v___x_105_);
lean_ctor_set(v___x_106_, 1, v___x_104_);
lean_ctor_set(v___x_106_, 2, v___x_103_);
return v___x_106_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grindTrace___closed__6(void){
_start:
{
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_107_ = lean_obj_once(&l_Lean_Parser_Tactic_grind___closed__28, &l_Lean_Parser_Tactic_grind___closed__28_once, _init_l_Lean_Parser_Tactic_grind___closed__28);
v___x_108_ = lean_obj_once(&l_Lean_Parser_Tactic_grindTrace___closed__5, &l_Lean_Parser_Tactic_grindTrace___closed__5_once, _init_l_Lean_Parser_Tactic_grindTrace___closed__5);
v___x_109_ = ((lean_object*)(l_Lean_Parser_Tactic_grind___closed__6));
v___x_110_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_110_, 0, v___x_109_);
lean_ctor_set(v___x_110_, 1, v___x_108_);
lean_ctor_set(v___x_110_, 2, v___x_107_);
return v___x_110_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grindTrace___closed__7(void){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_111_ = lean_obj_once(&l_Lean_Parser_Tactic_grindTrace___closed__6, &l_Lean_Parser_Tactic_grindTrace___closed__6_once, _init_l_Lean_Parser_Tactic_grindTrace___closed__6);
v___x_112_ = lean_unsigned_to_nat(1022u);
v___x_113_ = ((lean_object*)(l_Lean_Parser_Tactic_grindTrace___closed__1));
v___x_114_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_114_, 0, v___x_113_);
lean_ctor_set(v___x_114_, 1, v___x_112_);
lean_ctor_set(v___x_114_, 2, v___x_111_);
return v___x_114_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grindTrace(void){
_start:
{
lean_object* v___x_115_; 
v___x_115_ = lean_obj_once(&l_Lean_Parser_Tactic_grindTrace___closed__7, &l_Lean_Parser_Tactic_grindTrace___closed__7_once, _init_l_Lean_Parser_Tactic_grindTrace___closed__7);
return v___x_115_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_sym___closed__3(void){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_125_ = l_Lean_Parser_Tactic_optConfig;
v___x_126_ = ((lean_object*)(l_Lean_Parser_Tactic_sym___closed__2));
v___x_127_ = ((lean_object*)(l_Lean_Parser_Tactic_grind___closed__6));
v___x_128_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_128_, 0, v___x_127_);
lean_ctor_set(v___x_128_, 1, v___x_126_);
lean_ctor_set(v___x_128_, 2, v___x_125_);
return v___x_128_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_sym___closed__4(void){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_129_ = ((lean_object*)(l_Lean_Parser_Tactic_grind___closed__13));
v___x_130_ = lean_obj_once(&l_Lean_Parser_Tactic_sym___closed__3, &l_Lean_Parser_Tactic_sym___closed__3_once, _init_l_Lean_Parser_Tactic_sym___closed__3);
v___x_131_ = ((lean_object*)(l_Lean_Parser_Tactic_grind___closed__6));
v___x_132_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_132_, 0, v___x_131_);
lean_ctor_set(v___x_132_, 1, v___x_130_);
lean_ctor_set(v___x_132_, 2, v___x_129_);
return v___x_132_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_sym___closed__5(void){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_133_ = lean_obj_once(&l_Lean_Parser_Tactic_grind___closed__28, &l_Lean_Parser_Tactic_grind___closed__28_once, _init_l_Lean_Parser_Tactic_grind___closed__28);
v___x_134_ = lean_obj_once(&l_Lean_Parser_Tactic_sym___closed__4, &l_Lean_Parser_Tactic_sym___closed__4_once, _init_l_Lean_Parser_Tactic_sym___closed__4);
v___x_135_ = ((lean_object*)(l_Lean_Parser_Tactic_grind___closed__6));
v___x_136_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_136_, 0, v___x_135_);
lean_ctor_set(v___x_136_, 1, v___x_134_);
lean_ctor_set(v___x_136_, 2, v___x_133_);
return v___x_136_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_sym___closed__6(void){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_137_ = ((lean_object*)(l_Lean_Parser_Tactic_grind___closed__31));
v___x_138_ = lean_obj_once(&l_Lean_Parser_Tactic_sym___closed__5, &l_Lean_Parser_Tactic_sym___closed__5_once, _init_l_Lean_Parser_Tactic_sym___closed__5);
v___x_139_ = ((lean_object*)(l_Lean_Parser_Tactic_grind___closed__6));
v___x_140_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_140_, 0, v___x_139_);
lean_ctor_set(v___x_140_, 1, v___x_138_);
lean_ctor_set(v___x_140_, 2, v___x_137_);
return v___x_140_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_sym___closed__7(void){
_start:
{
lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_141_ = l_Lean_Parser_Tactic_Grind_grindSeq;
v___x_142_ = lean_obj_once(&l_Lean_Parser_Tactic_sym___closed__6, &l_Lean_Parser_Tactic_sym___closed__6_once, _init_l_Lean_Parser_Tactic_sym___closed__6);
v___x_143_ = ((lean_object*)(l_Lean_Parser_Tactic_grind___closed__6));
v___x_144_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_144_, 0, v___x_143_);
lean_ctor_set(v___x_144_, 1, v___x_142_);
lean_ctor_set(v___x_144_, 2, v___x_141_);
return v___x_144_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_sym___closed__8(void){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_145_ = lean_obj_once(&l_Lean_Parser_Tactic_sym___closed__7, &l_Lean_Parser_Tactic_sym___closed__7_once, _init_l_Lean_Parser_Tactic_sym___closed__7);
v___x_146_ = lean_unsigned_to_nat(1022u);
v___x_147_ = ((lean_object*)(l_Lean_Parser_Tactic_sym___closed__1));
v___x_148_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_148_, 0, v___x_147_);
lean_ctor_set(v___x_148_, 1, v___x_146_);
lean_ctor_set(v___x_148_, 2, v___x_145_);
return v___x_148_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_sym(void){
_start:
{
lean_object* v___x_149_; 
v___x_149_ = lean_obj_once(&l_Lean_Parser_Tactic_sym___closed__8, &l_Lean_Parser_Tactic_sym___closed__8_once, _init_l_Lean_Parser_Tactic_sym___closed__8);
return v___x_149_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_cutsat___closed__3(void){
_start:
{
lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_159_ = l_Lean_Parser_Tactic_optConfig;
v___x_160_ = ((lean_object*)(l_Lean_Parser_Tactic_cutsat___closed__2));
v___x_161_ = ((lean_object*)(l_Lean_Parser_Tactic_grind___closed__6));
v___x_162_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_162_, 0, v___x_161_);
lean_ctor_set(v___x_162_, 1, v___x_160_);
lean_ctor_set(v___x_162_, 2, v___x_159_);
return v___x_162_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_cutsat___closed__4(void){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_163_ = lean_obj_once(&l_Lean_Parser_Tactic_cutsat___closed__3, &l_Lean_Parser_Tactic_cutsat___closed__3_once, _init_l_Lean_Parser_Tactic_cutsat___closed__3);
v___x_164_ = lean_unsigned_to_nat(1022u);
v___x_165_ = ((lean_object*)(l_Lean_Parser_Tactic_cutsat___closed__1));
v___x_166_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_166_, 0, v___x_165_);
lean_ctor_set(v___x_166_, 1, v___x_164_);
lean_ctor_set(v___x_166_, 2, v___x_163_);
return v___x_166_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_cutsat(void){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = lean_obj_once(&l_Lean_Parser_Tactic_cutsat___closed__4, &l_Lean_Parser_Tactic_cutsat___closed__4_once, _init_l_Lean_Parser_Tactic_cutsat___closed__4);
return v___x_167_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_lia___closed__3(void){
_start:
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_177_ = l_Lean_Parser_Tactic_optConfig;
v___x_178_ = ((lean_object*)(l_Lean_Parser_Tactic_lia___closed__2));
v___x_179_ = ((lean_object*)(l_Lean_Parser_Tactic_grind___closed__6));
v___x_180_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_180_, 0, v___x_179_);
lean_ctor_set(v___x_180_, 1, v___x_178_);
lean_ctor_set(v___x_180_, 2, v___x_177_);
return v___x_180_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_lia___closed__4(void){
_start:
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_181_ = lean_obj_once(&l_Lean_Parser_Tactic_lia___closed__3, &l_Lean_Parser_Tactic_lia___closed__3_once, _init_l_Lean_Parser_Tactic_lia___closed__3);
v___x_182_ = lean_unsigned_to_nat(1022u);
v___x_183_ = ((lean_object*)(l_Lean_Parser_Tactic_lia___closed__1));
v___x_184_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_184_, 0, v___x_183_);
lean_ctor_set(v___x_184_, 1, v___x_182_);
lean_ctor_set(v___x_184_, 2, v___x_181_);
return v___x_184_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_lia(void){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = lean_obj_once(&l_Lean_Parser_Tactic_lia___closed__4, &l_Lean_Parser_Tactic_lia___closed__4_once, _init_l_Lean_Parser_Tactic_lia___closed__4);
return v___x_185_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grind__order___closed__3(void){
_start:
{
lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_195_ = l_Lean_Parser_Tactic_optConfig;
v___x_196_ = ((lean_object*)(l_Lean_Parser_Tactic_grind__order___closed__2));
v___x_197_ = ((lean_object*)(l_Lean_Parser_Tactic_grind___closed__6));
v___x_198_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_198_, 0, v___x_197_);
lean_ctor_set(v___x_198_, 1, v___x_196_);
lean_ctor_set(v___x_198_, 2, v___x_195_);
return v___x_198_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grind__order___closed__4(void){
_start:
{
lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_199_ = lean_obj_once(&l_Lean_Parser_Tactic_grind__order___closed__3, &l_Lean_Parser_Tactic_grind__order___closed__3_once, _init_l_Lean_Parser_Tactic_grind__order___closed__3);
v___x_200_ = lean_unsigned_to_nat(1022u);
v___x_201_ = ((lean_object*)(l_Lean_Parser_Tactic_grind__order___closed__1));
v___x_202_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_202_, 0, v___x_201_);
lean_ctor_set(v___x_202_, 1, v___x_200_);
lean_ctor_set(v___x_202_, 2, v___x_199_);
return v___x_202_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grind__order(void){
_start:
{
lean_object* v___x_203_; 
v___x_203_ = lean_obj_once(&l_Lean_Parser_Tactic_grind__order___closed__4, &l_Lean_Parser_Tactic_grind__order___closed__4_once, _init_l_Lean_Parser_Tactic_grind__order___closed__4);
return v___x_203_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grind__linarith___closed__3(void){
_start:
{
lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_213_ = l_Lean_Parser_Tactic_optConfig;
v___x_214_ = ((lean_object*)(l_Lean_Parser_Tactic_grind__linarith___closed__2));
v___x_215_ = ((lean_object*)(l_Lean_Parser_Tactic_grind___closed__6));
v___x_216_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_216_, 0, v___x_215_);
lean_ctor_set(v___x_216_, 1, v___x_214_);
lean_ctor_set(v___x_216_, 2, v___x_213_);
return v___x_216_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grind__linarith___closed__4(void){
_start:
{
lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_217_ = lean_obj_once(&l_Lean_Parser_Tactic_grind__linarith___closed__3, &l_Lean_Parser_Tactic_grind__linarith___closed__3_once, _init_l_Lean_Parser_Tactic_grind__linarith___closed__3);
v___x_218_ = lean_unsigned_to_nat(1022u);
v___x_219_ = ((lean_object*)(l_Lean_Parser_Tactic_grind__linarith___closed__1));
v___x_220_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_220_, 0, v___x_219_);
lean_ctor_set(v___x_220_, 1, v___x_218_);
lean_ctor_set(v___x_220_, 2, v___x_217_);
return v___x_220_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grind__linarith(void){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = lean_obj_once(&l_Lean_Parser_Tactic_grind__linarith___closed__4, &l_Lean_Parser_Tactic_grind__linarith___closed__4_once, _init_l_Lean_Parser_Tactic_grind__linarith___closed__4);
return v___x_221_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grobner___closed__3(void){
_start:
{
lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_231_ = l_Lean_Parser_Tactic_optConfig;
v___x_232_ = ((lean_object*)(l_Lean_Parser_Tactic_grobner___closed__2));
v___x_233_ = ((lean_object*)(l_Lean_Parser_Tactic_grind___closed__6));
v___x_234_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_234_, 0, v___x_233_);
lean_ctor_set(v___x_234_, 1, v___x_232_);
lean_ctor_set(v___x_234_, 2, v___x_231_);
return v___x_234_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grobner___closed__4(void){
_start:
{
lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_235_ = lean_obj_once(&l_Lean_Parser_Tactic_grobner___closed__3, &l_Lean_Parser_Tactic_grobner___closed__3_once, _init_l_Lean_Parser_Tactic_grobner___closed__3);
v___x_236_ = lean_unsigned_to_nat(1022u);
v___x_237_ = ((lean_object*)(l_Lean_Parser_Tactic_grobner___closed__1));
v___x_238_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_238_, 0, v___x_237_);
lean_ctor_set(v___x_238_, 1, v___x_236_);
lean_ctor_set(v___x_238_, 2, v___x_235_);
return v___x_238_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grobner(void){
_start:
{
lean_object* v___x_239_; 
v___x_239_ = lean_obj_once(&l_Lean_Parser_Tactic_grobner___closed__4, &l_Lean_Parser_Tactic_grobner___closed__4_once, _init_l_Lean_Parser_Tactic_grobner___closed__4);
return v___x_239_;
}
}
lean_object* runtime_initialize_Init_Core(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Interactive(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Grind_Tactics(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Core(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Interactive(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Grind_Tactics(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Lean_Parser_Tactic_grind = _init_l_Lean_Parser_Tactic_grind();
lean_mark_persistent(l_Lean_Parser_Tactic_grind);
l_Lean_Parser_Tactic_grindTrace = _init_l_Lean_Parser_Tactic_grindTrace();
lean_mark_persistent(l_Lean_Parser_Tactic_grindTrace);
l_Lean_Parser_Tactic_sym = _init_l_Lean_Parser_Tactic_sym();
lean_mark_persistent(l_Lean_Parser_Tactic_sym);
l_Lean_Parser_Tactic_cutsat = _init_l_Lean_Parser_Tactic_cutsat();
lean_mark_persistent(l_Lean_Parser_Tactic_cutsat);
l_Lean_Parser_Tactic_lia = _init_l_Lean_Parser_Tactic_lia();
lean_mark_persistent(l_Lean_Parser_Tactic_lia);
l_Lean_Parser_Tactic_grind__order = _init_l_Lean_Parser_Tactic_grind__order();
lean_mark_persistent(l_Lean_Parser_Tactic_grind__order);
l_Lean_Parser_Tactic_grind__linarith = _init_l_Lean_Parser_Tactic_grind__linarith();
lean_mark_persistent(l_Lean_Parser_Tactic_grind__linarith);
l_Lean_Parser_Tactic_grobner = _init_l_Lean_Parser_Tactic_grobner();
lean_mark_persistent(l_Lean_Parser_Tactic_grobner);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Core(uint8_t builtin);
lean_object* initialize_Init_Grind_Interactive(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Grind_Tactics(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Core(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Interactive(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Grind_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Grind_Tactics(builtin);
}
#ifdef __cplusplus
}
#endif

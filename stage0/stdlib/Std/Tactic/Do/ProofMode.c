// Lean compiler output
// Module: Std.Tactic.Do.ProofMode
// Imports: public import Std.Do.SPred.SPred
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
static const lean_string_object l_Std_Tactic_Do_mgoalHyp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "mgoalHyp"};
static const lean_object* l_Std_Tactic_Do_mgoalHyp___closed__0 = (const lean_object*)&l_Std_Tactic_Do_mgoalHyp___closed__0_value;
static const lean_string_object l_Std_Tactic_Do_mgoalHyp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Std_Tactic_Do_mgoalHyp___closed__1 = (const lean_object*)&l_Std_Tactic_Do_mgoalHyp___closed__1_value;
static const lean_string_object l_Std_Tactic_Do_mgoalHyp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Std_Tactic_Do_mgoalHyp___closed__2 = (const lean_object*)&l_Std_Tactic_Do_mgoalHyp___closed__2_value;
static const lean_string_object l_Std_Tactic_Do_mgoalHyp___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l_Std_Tactic_Do_mgoalHyp___closed__3 = (const lean_object*)&l_Std_Tactic_Do_mgoalHyp___closed__3_value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_Tactic_Do_mgoalHyp___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Tactic_Do_mgoalHyp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Tactic_Do_mgoalHyp___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Tactic_Do_mgoalHyp___closed__4_value_aux_0),((lean_object*)&l_Std_Tactic_Do_mgoalHyp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Std_Tactic_Do_mgoalHyp___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Tactic_Do_mgoalHyp___closed__4_value_aux_1),((lean_object*)&l_Std_Tactic_Do_mgoalHyp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(193, 32, 213, 253, 69, 208, 115, 14)}};
static const lean_ctor_object l_Std_Tactic_Do_mgoalHyp___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Tactic_Do_mgoalHyp___closed__4_value_aux_2),((lean_object*)&l_Std_Tactic_Do_mgoalHyp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(3, 150, 110, 128, 2, 249, 81, 25)}};
static const lean_object* l_Std_Tactic_Do_mgoalHyp___closed__4 = (const lean_object*)&l_Std_Tactic_Do_mgoalHyp___closed__4_value;
static const lean_string_object l_Std_Tactic_Do_mgoalHyp___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Std_Tactic_Do_mgoalHyp___closed__5 = (const lean_object*)&l_Std_Tactic_Do_mgoalHyp___closed__5_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Std_Tactic_Do_mgoalHyp___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Tactic_Do_mgoalHyp___closed__5_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Std_Tactic_Do_mgoalHyp___closed__6 = (const lean_object*)&l_Std_Tactic_Do_mgoalHyp___closed__6_value;
static const lean_string_object l_Std_Tactic_Do_mgoalHyp___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Std_Tactic_Do_mgoalHyp___closed__7 = (const lean_object*)&l_Std_Tactic_Do_mgoalHyp___closed__7_value;
static const lean_ctor_object l_Std_Tactic_Do_mgoalHyp___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Tactic_Do_mgoalHyp___closed__7_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Std_Tactic_Do_mgoalHyp___closed__8 = (const lean_object*)&l_Std_Tactic_Do_mgoalHyp___closed__8_value;
static const lean_ctor_object l_Std_Tactic_Do_mgoalHyp___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Tactic_Do_mgoalHyp___closed__8_value)}};
static const lean_object* l_Std_Tactic_Do_mgoalHyp___closed__9 = (const lean_object*)&l_Std_Tactic_Do_mgoalHyp___closed__9_value;
static const lean_string_object l_Std_Tactic_Do_mgoalHyp___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " : "};
static const lean_object* l_Std_Tactic_Do_mgoalHyp___closed__10 = (const lean_object*)&l_Std_Tactic_Do_mgoalHyp___closed__10_value;
static const lean_ctor_object l_Std_Tactic_Do_mgoalHyp___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Tactic_Do_mgoalHyp___closed__10_value)}};
static const lean_object* l_Std_Tactic_Do_mgoalHyp___closed__11 = (const lean_object*)&l_Std_Tactic_Do_mgoalHyp___closed__11_value;
static const lean_ctor_object l_Std_Tactic_Do_mgoalHyp___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Tactic_Do_mgoalHyp___closed__6_value),((lean_object*)&l_Std_Tactic_Do_mgoalHyp___closed__9_value),((lean_object*)&l_Std_Tactic_Do_mgoalHyp___closed__11_value)}};
static const lean_object* l_Std_Tactic_Do_mgoalHyp___closed__12 = (const lean_object*)&l_Std_Tactic_Do_mgoalHyp___closed__12_value;
static const lean_string_object l_Std_Tactic_Do_mgoalHyp___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Std_Tactic_Do_mgoalHyp___closed__13 = (const lean_object*)&l_Std_Tactic_Do_mgoalHyp___closed__13_value;
static const lean_ctor_object l_Std_Tactic_Do_mgoalHyp___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Tactic_Do_mgoalHyp___closed__13_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Std_Tactic_Do_mgoalHyp___closed__14 = (const lean_object*)&l_Std_Tactic_Do_mgoalHyp___closed__14_value;
static const lean_ctor_object l_Std_Tactic_Do_mgoalHyp___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Std_Tactic_Do_mgoalHyp___closed__14_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Tactic_Do_mgoalHyp___closed__15 = (const lean_object*)&l_Std_Tactic_Do_mgoalHyp___closed__15_value;
static const lean_ctor_object l_Std_Tactic_Do_mgoalHyp___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Tactic_Do_mgoalHyp___closed__6_value),((lean_object*)&l_Std_Tactic_Do_mgoalHyp___closed__12_value),((lean_object*)&l_Std_Tactic_Do_mgoalHyp___closed__15_value)}};
static const lean_object* l_Std_Tactic_Do_mgoalHyp___closed__16 = (const lean_object*)&l_Std_Tactic_Do_mgoalHyp___closed__16_value;
static const lean_ctor_object l_Std_Tactic_Do_mgoalHyp___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Std_Tactic_Do_mgoalHyp___closed__0_value),((lean_object*)&l_Std_Tactic_Do_mgoalHyp___closed__4_value),((lean_object*)&l_Std_Tactic_Do_mgoalHyp___closed__16_value)}};
static const lean_object* l_Std_Tactic_Do_mgoalHyp___closed__17 = (const lean_object*)&l_Std_Tactic_Do_mgoalHyp___closed__17_value;
LEAN_EXPORT const lean_object* l_Std_Tactic_Do_mgoalHyp = (const lean_object*)&l_Std_Tactic_Do_mgoalHyp___closed__17_value;
static const lean_string_object l_Std_Tactic_Do_mgoalStx___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "mgoalStx"};
static const lean_object* l_Std_Tactic_Do_mgoalStx___closed__0 = (const lean_object*)&l_Std_Tactic_Do_mgoalStx___closed__0_value;
static const lean_ctor_object l_Std_Tactic_Do_mgoalStx___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Tactic_Do_mgoalHyp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Tactic_Do_mgoalStx___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Tactic_Do_mgoalStx___closed__1_value_aux_0),((lean_object*)&l_Std_Tactic_Do_mgoalHyp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Std_Tactic_Do_mgoalStx___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Tactic_Do_mgoalStx___closed__1_value_aux_1),((lean_object*)&l_Std_Tactic_Do_mgoalHyp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(193, 32, 213, 253, 69, 208, 115, 14)}};
static const lean_ctor_object l_Std_Tactic_Do_mgoalStx___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Tactic_Do_mgoalStx___closed__1_value_aux_2),((lean_object*)&l_Std_Tactic_Do_mgoalStx___closed__0_value),LEAN_SCALAR_PTR_LITERAL(192, 235, 142, 175, 247, 121, 9, 33)}};
static const lean_object* l_Std_Tactic_Do_mgoalStx___closed__1 = (const lean_object*)&l_Std_Tactic_Do_mgoalStx___closed__1_value;
static const lean_string_object l_Std_Tactic_Do_mgoalStx___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "many"};
static const lean_object* l_Std_Tactic_Do_mgoalStx___closed__2 = (const lean_object*)&l_Std_Tactic_Do_mgoalStx___closed__2_value;
static const lean_ctor_object l_Std_Tactic_Do_mgoalStx___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Tactic_Do_mgoalStx___closed__2_value),LEAN_SCALAR_PTR_LITERAL(41, 35, 40, 86, 189, 97, 244, 31)}};
static const lean_object* l_Std_Tactic_Do_mgoalStx___closed__3 = (const lean_object*)&l_Std_Tactic_Do_mgoalStx___closed__3_value;
static const lean_string_object l_Std_Tactic_Do_mgoalStx___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ppDedent"};
static const lean_object* l_Std_Tactic_Do_mgoalStx___closed__4 = (const lean_object*)&l_Std_Tactic_Do_mgoalStx___closed__4_value;
static const lean_ctor_object l_Std_Tactic_Do_mgoalStx___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Tactic_Do_mgoalStx___closed__4_value),LEAN_SCALAR_PTR_LITERAL(242, 37, 230, 124, 106, 100, 159, 37)}};
static const lean_object* l_Std_Tactic_Do_mgoalStx___closed__5 = (const lean_object*)&l_Std_Tactic_Do_mgoalStx___closed__5_value;
static const lean_string_object l_Std_Tactic_Do_mgoalStx___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ppLine"};
static const lean_object* l_Std_Tactic_Do_mgoalStx___closed__6 = (const lean_object*)&l_Std_Tactic_Do_mgoalStx___closed__6_value;
static const lean_ctor_object l_Std_Tactic_Do_mgoalStx___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Tactic_Do_mgoalStx___closed__6_value),LEAN_SCALAR_PTR_LITERAL(117, 61, 38, 245, 158, 59, 171, 58)}};
static const lean_object* l_Std_Tactic_Do_mgoalStx___closed__7 = (const lean_object*)&l_Std_Tactic_Do_mgoalStx___closed__7_value;
static const lean_ctor_object l_Std_Tactic_Do_mgoalStx___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Tactic_Do_mgoalStx___closed__7_value)}};
static const lean_object* l_Std_Tactic_Do_mgoalStx___closed__8 = (const lean_object*)&l_Std_Tactic_Do_mgoalStx___closed__8_value;
static const lean_ctor_object l_Std_Tactic_Do_mgoalStx___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Tactic_Do_mgoalHyp___closed__6_value),((lean_object*)&l_Std_Tactic_Do_mgoalStx___closed__8_value),((lean_object*)&l_Std_Tactic_Do_mgoalHyp___closed__17_value)}};
static const lean_object* l_Std_Tactic_Do_mgoalStx___closed__9 = (const lean_object*)&l_Std_Tactic_Do_mgoalStx___closed__9_value;
static const lean_ctor_object l_Std_Tactic_Do_mgoalStx___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Tactic_Do_mgoalStx___closed__5_value),((lean_object*)&l_Std_Tactic_Do_mgoalStx___closed__9_value)}};
static const lean_object* l_Std_Tactic_Do_mgoalStx___closed__10 = (const lean_object*)&l_Std_Tactic_Do_mgoalStx___closed__10_value;
static const lean_ctor_object l_Std_Tactic_Do_mgoalStx___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Tactic_Do_mgoalStx___closed__3_value),((lean_object*)&l_Std_Tactic_Do_mgoalStx___closed__10_value)}};
static const lean_object* l_Std_Tactic_Do_mgoalStx___closed__11 = (const lean_object*)&l_Std_Tactic_Do_mgoalStx___closed__11_value;
static const lean_string_object l_Std_Tactic_Do_mgoalStx___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 3, .m_data = "⊢ₛ "};
static const lean_object* l_Std_Tactic_Do_mgoalStx___closed__12 = (const lean_object*)&l_Std_Tactic_Do_mgoalStx___closed__12_value;
static const lean_ctor_object l_Std_Tactic_Do_mgoalStx___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Tactic_Do_mgoalStx___closed__12_value)}};
static const lean_object* l_Std_Tactic_Do_mgoalStx___closed__13 = (const lean_object*)&l_Std_Tactic_Do_mgoalStx___closed__13_value;
static const lean_ctor_object l_Std_Tactic_Do_mgoalStx___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Tactic_Do_mgoalHyp___closed__6_value),((lean_object*)&l_Std_Tactic_Do_mgoalStx___closed__8_value),((lean_object*)&l_Std_Tactic_Do_mgoalStx___closed__13_value)}};
static const lean_object* l_Std_Tactic_Do_mgoalStx___closed__14 = (const lean_object*)&l_Std_Tactic_Do_mgoalStx___closed__14_value;
static const lean_ctor_object l_Std_Tactic_Do_mgoalStx___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Tactic_Do_mgoalHyp___closed__6_value),((lean_object*)&l_Std_Tactic_Do_mgoalStx___closed__14_value),((lean_object*)&l_Std_Tactic_Do_mgoalHyp___closed__15_value)}};
static const lean_object* l_Std_Tactic_Do_mgoalStx___closed__15 = (const lean_object*)&l_Std_Tactic_Do_mgoalStx___closed__15_value;
static const lean_ctor_object l_Std_Tactic_Do_mgoalStx___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Tactic_Do_mgoalStx___closed__5_value),((lean_object*)&l_Std_Tactic_Do_mgoalStx___closed__15_value)}};
static const lean_object* l_Std_Tactic_Do_mgoalStx___closed__16 = (const lean_object*)&l_Std_Tactic_Do_mgoalStx___closed__16_value;
static const lean_ctor_object l_Std_Tactic_Do_mgoalStx___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Tactic_Do_mgoalHyp___closed__6_value),((lean_object*)&l_Std_Tactic_Do_mgoalStx___closed__11_value),((lean_object*)&l_Std_Tactic_Do_mgoalStx___closed__16_value)}};
static const lean_object* l_Std_Tactic_Do_mgoalStx___closed__17 = (const lean_object*)&l_Std_Tactic_Do_mgoalStx___closed__17_value;
static const lean_ctor_object l_Std_Tactic_Do_mgoalStx___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Std_Tactic_Do_mgoalStx___closed__0_value),((lean_object*)&l_Std_Tactic_Do_mgoalStx___closed__1_value),((lean_object*)&l_Std_Tactic_Do_mgoalStx___closed__17_value)}};
static const lean_object* l_Std_Tactic_Do_mgoalStx___closed__18 = (const lean_object*)&l_Std_Tactic_Do_mgoalStx___closed__18_value;
LEAN_EXPORT const lean_object* l_Std_Tactic_Do_mgoalStx = (const lean_object*)&l_Std_Tactic_Do_mgoalStx___closed__18_value;
lean_object* initialize_Std_Do_SPred_SPred(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_Do_ProofMode(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Do_SPred_SPred(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
